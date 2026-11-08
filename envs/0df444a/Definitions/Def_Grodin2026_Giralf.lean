-- Prove2me | Definitions.Def_Grodin2026_Giralf
-- name    : Grodin2026_Giralf
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T17:17:44.656918+00:00
-- url     : https://prove2.me/theorems/4b2c1130-97cb-42b5-8dc9-6f3aad605b17
-- title:
--   Section 5: Giralf Graded Judgments, Positive AARA Types, Insertion Sort, and Cost Inference Annotations
-- statement:
--   Formalizes Section 5 of Grodin, Chu, Li, Hoffmann & Harper (2026): cartesian (lazy) products `ProdComp` and coproducts `SumComp` of computation types, the Calf semantics of Giralf judgments `GiralfSemJudgment Delta A q` ($\triangleright^q \Delta \mathrel{\multimap\!\!\!\!+} A$, §5.2), pre-payment `prepayGiralf` (Remark 5.5), `giralfStore`, `giralfSpend`, `giralfPair`, `giralfProj1`, `giralfProj2`, `giralfGet`, and `giralfPay` (§5.1), the positive AARA type grammar `AARAType`, value sets `aaraValues` ($\llbracket A \rrbracket$), potential functions `aaraPotential` ($\Phi_A : \llbracket A \rrbracket \to \mathbb{N}$, Figure 2), compositional Calf interpretation `interpAARAType` (Theorem 5.7), cost-instrumented insertion sort `insertCostTop` and `isortCostTop` (Examples 5.2, 5.3, 5.18), `CostInferenceCertificate` (Definition 5.9), and skeletal recursor annotations `ListRecAnnotation`, `ValidSnocRecAnnotation`, and `snocSymbolicAnnotation` (Lemmas 5.15-5.16, Examples 5.14 & 5.17).
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Section 5, pp. 17-24.

import Definitions.Def_Grodin2026_Banker

/-!
# Giralf: A Graded, Inferential, Resource-Aware Logical Framework (Grodin et al., 2026, §5)

Constructive Lean 4 formalization of Section 5 of:
Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper (2026),
*Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost*
(`arXiv:2607.08547v2`).

This module formalizes:
- **§5.1:** The graded judgment structure $\Delta \vdash^q e : A$ of Giralf, standard linear and
  negative types (lazy products $A_1 \times A_2$), credit/debit rules (`store⟨p⟩`, `release`,
  `get⟨p⟩`, `pay`), linear- and quadratic-credit list rules, the derivable credit-aware
  paramorphism (Lemma 5.1), and insertion sort (`insert` and `isort`, Examples 5.2–5.3).
- **§5.2:** The resource-aware Calf semantics of $\Delta \vdash^q e : A$ as a lax homomorphism
  $\triangleright^q(\bigotimes \Delta) \mathrel{\multimap\!\!\!\!+} A$, pre-paying via
  $e \circ \mathsf{save}\langle q \rangle$ (Remark 5.5), the positive AARA type grammar, values
  $\llbracket A \rrbracket$, and potential functions $\Phi_A : \llbracket A \rrbracket \to \mathbb{N}$
  (Figure 2), the Calf interpretation of AARA types (Theorem 5.7), and Soundness of AARA
  (Theorem 5.8).
- **§5.3:** Cost inference $a : \underline{A} \vdash^q \underline{e} : \underline{B}$
  (Definition 5.9), concrete $\neg\mathsf{abs}$ erasure (Lemma 5.10, Corollary 5.11), skeletal type
  translations and pointwise operations $\oplus$ and $k \odot -$ on cost-free and cost-aware
  annotations (Lemmas 5.15–5.16), and the `snoc` / `isort` inference examples
  (Examples 5.13, 5.14, 5.17, 5.18).
-/

namespace Grodin2026

/-! ## §5.1–5.2 Positive & Negative Calf Connectives and Graded Giralf Semantics -/

/-- Cartesian (lazy) product $A_1 \times A_2$ of single-world cost algebras (§5.1.1):
carrier is $UA_1 \times UA_2$ with componentwise cost action
$\mathsf{charge}_{A_1 \times A_2}\langle c \rangle(a_1, a_2) =
(\mathsf{charge}_{A_1}\langle c \rangle(a_1), \mathsf{charge}_{A_2}\langle c \rangle(a_2))$. -/
def ProdCostAlg (A₁ A₂ : CostAlg) : CostAlg where
  carrier := A₁.carrier × A₂.carrier
  le := fun p q => A₁.le p.1 q.1 ∧ A₂.le p.2 q.2
  le_refl := fun p => ⟨A₁.le_refl p.1, A₂.le_refl p.2⟩
  le_trans := fun ⟨h₁, h₂⟩ ⟨k₁, k₂⟩ => ⟨A₁.le_trans h₁ k₁, A₂.le_trans h₂ k₂⟩
  charge := fun c p => (A₁.charge c p.1, A₂.charge c p.2)
  charge_zero := fun p => Prod.ext (A₁.charge_zero p.1) (A₂.charge_zero p.2)
  charge_add := fun c₁ c₂ p => Prod.ext (A₁.charge_add c₁ c₂ p.1) (A₂.charge_add c₁ c₂ p.2)
  charge_mono_cost := fun p h => ⟨A₁.charge_mono_cost p.1 h, A₂.charge_mono_cost p.2 h⟩
  charge_mono_val := fun c {_ _} ⟨h₁, h₂⟩ => ⟨A₁.charge_mono_val c h₁, A₂.charge_mono_val c h₂⟩

/-- Lazy product $A_1 \times A_2$ of phased computation types in $\mathcal{C}$ (§5.1.1). -/
def ProdComp (A₁ A₂ : CompType) : CompType where
  top := ProdCostAlg A₁.top A₂.top
  abs := ProdCostAlg A₁.abs A₂.abs
  alpha := {
    fn := fun p => (A₁.alpha.fn p.1, A₂.alpha.fn p.2)
    map_charge := fun c p => Prod.ext (A₁.alpha.map_charge c p.1) (A₂.alpha.map_charge c p.2)
    mono := fun ⟨h₁, h₂⟩ => ⟨A₁.alpha.mono h₁, A₂.alpha.mono h₂⟩
  }

/-- Coproduct (sum) $A_1 + A_2$ of single-world cost algebras (§2, p. 4 & Figure 2):
carrier is $UA_1 \oplus UA_2$ with cost action acting on the active summand. -/
def SumCostAlg (A₁ A₂ : CostAlg) : CostAlg where
  carrier := Sum A₁.carrier A₂.carrier
  le := fun s₁ s₂ =>
    match s₁, s₂ with
    | .inl a₁, .inl b₁ => A₁.le a₁ b₁
    | .inr a₂, .inr b₂ => A₂.le a₂ b₂
    | _, _ => False
  le_refl := fun s =>
    match s with
    | .inl a₁ => A₁.le_refl a₁
    | .inr a₂ => A₂.le_refl a₂
  le_trans := by
    intro s₁ s₂ s₃ h₁₂ h₂₃
    cases s₁ <;> cases s₂ <;> cases s₃
    · exact A₁.le_trans h₁₂ h₂₃
    · exact False.elim h₂₃
    · exact False.elim h₁₂
    · exact False.elim h₁₂
    · exact False.elim h₁₂
    · exact False.elim h₁₂
    · exact False.elim h₂₃
    · exact A₂.le_trans h₁₂ h₂₃
  charge := fun c s =>
    match s with
    | .inl a₁ => .inl (A₁.charge c a₁)
    | .inr a₂ => .inr (A₂.charge c a₂)
  charge_zero := fun s =>
    match s with
    | .inl a₁ => congrArg Sum.inl (A₁.charge_zero a₁)
    | .inr a₂ => congrArg Sum.inr (A₂.charge_zero a₂)
  charge_add := fun c₁ c₂ s =>
    match s with
    | .inl a₁ => congrArg Sum.inl (A₁.charge_add c₁ c₂ a₁)
    | .inr a₂ => congrArg Sum.inr (A₂.charge_add c₁ c₂ a₂)
  charge_mono_cost := fun s h =>
    match s with
    | .inl a₁ => A₁.charge_mono_cost a₁ h
    | .inr a₂ => A₂.charge_mono_cost a₂ h
  charge_mono_val := by
    intro c s₁ s₂ h
    cases s₁ <;> cases s₂
    · exact A₁.charge_mono_val c h
    · exact False.elim h
    · exact False.elim h
    · exact A₂.charge_mono_val c h

/-- Coproduct (sum) $A_1 + A_2$ of phased computation types in $\mathcal{C}$. -/
def SumComp (A₁ A₂ : CompType) : CompType where
  top := SumCostAlg A₁.top A₂.top
  abs := SumCostAlg A₁.abs A₂.abs
  alpha := {
    fn := fun s =>
      match s with
      | .inl a₁ => .inl (A₁.alpha.fn a₁)
      | .inr a₂ => .inr (A₂.alpha.fn a₂)
    map_charge := fun c s =>
      match s with
      | .inl a₁ => congrArg Sum.inl (A₁.alpha.map_charge c a₁)
      | .inr a₂ => congrArg Sum.inr (A₂.alpha.map_charge c a₂)
    mono := by
      intro s₁ s₂ h
      cases s₁ <;> cases s₂
      · exact A₁.alpha.mono h
      · exact False.elim h
      · exact False.elim h
      · exact A₂.alpha.mono h
  }

/-- **Section 5.2 (Resource-Aware Semantics of Giralf Judgments):**
A Giralf typing judgment $\Delta \vdash^q e : A$ is interpreted in Calf as a lax homomorphism
$\triangleright^q \Delta \mathrel{\multimap\!\!\!\!+} A$. -/
abbrev GiralfSemJudgment (Delta A : CompType) (q : Nat) : Type :=
  LaxCompHom (CreditComp q Delta) A

/-- **Remark 5.5 (Pre-Paying for the Credit Context):**
Given a Giralf program $e : \triangleright^q \Delta \mathrel{\multimap\!\!\!\!+} A$, pre-paying for
the $q$ credits via $e \circ \mathsf{save}\langle q \rangle : \Delta \mathrel{\multimap\!\!\!\!+} A$
reframes the credit context $q$ as the amortized cost publicized in the abstract phase. -/
def prepayGiralf {Delta A : CompType} {q : Nat} (e : GiralfSemJudgment Delta A q) :
    LaxCompHom Delta A :=
  e.comp (saveComp q Delta).toLax

/-- **Example 5.4 (Semantics of `store⟨p⟩(e)` in Giralf):**
Given $q \ge p + q'$ and $e : \triangleright^{q'} \Delta \mathrel{\multimap\!\!\!\!+} A$,
$\mathsf{store}\langle p \rangle(e) : \triangleright^q \Delta \mathrel{\multimap\!\!\!\!+} \triangleright^p A$
weakens $\triangleright^q \Delta$ to $\triangleright^{p + q'} \Delta = \triangleright^p(\triangleright^{q'} \Delta)$
and applies $\triangleright^p e$. -/
def giralfStore {Delta A : CompType} {q p q' : Nat} (h : p + q' ≤ q)
    (e : GiralfSemJudgment Delta A q') :
    GiralfSemJudgment Delta (CreditComp p A) q where
  hom_top := e.hom_top
  hom_abs := e.hom_abs
  lax_comm := fun (d : Delta.top.carrier) => by
    change A.abs.le (A.abs.charge p (A.alpha.fn (e.hom_top.fn d)))
      (e.hom_abs.fn (Delta.abs.charge q (Delta.alpha.fn d)))
    have h₁ : A.abs.le
        (A.abs.charge p (A.alpha.fn (e.hom_top.fn d)))
        (A.abs.charge p (e.hom_abs.fn (Delta.abs.charge q' (Delta.alpha.fn d)))) :=
      A.abs.charge_mono_val p (e.lax_comm d)
    have h₂ : A.abs.charge p (e.hom_abs.fn (Delta.abs.charge q' (Delta.alpha.fn d))) =
        e.hom_abs.fn (Delta.abs.charge (p + q') (Delta.alpha.fn d)) := by
      calc A.abs.charge p (e.hom_abs.fn (Delta.abs.charge q' (Delta.alpha.fn d)))
        _ = e.hom_abs.fn (Delta.abs.charge p (Delta.abs.charge q' (Delta.alpha.fn d))) :=
          (e.hom_abs.map_charge p (Delta.abs.charge q' (Delta.alpha.fn d))).symm
        _ = e.hom_abs.fn (Delta.abs.charge (p + q') (Delta.alpha.fn d)) :=
          congrArg e.hom_abs.fn (Delta.abs.charge_add p q' (Delta.alpha.fn d)).symm
    rw [h₂] at h₁
    exact A.abs.le_trans h₁
      (e.hom_abs.mono (Delta.abs.charge_mono_cost (Delta.alpha.fn d) h))

/-- **Example 5.4 (Semantics of `spend⟨p⟩(e)` in Giralf):**
Post-composes `giralfStore h e` with $\mathsf{spend}\langle p \rangle : \triangleright^p A \multimap A$. -/
def giralfSpend {Delta A : CompType} {q p q' : Nat} (h : p + q' ≤ q)
    (e : GiralfSemJudgment Delta A q') :
    GiralfSemJudgment Delta A q :=
  (spendComp p A).toLax.comp (giralfStore h e)

/-- **Section 5.1.1 (Lazy Product Introduction in Giralf):**
From $\Delta \vdash^q e_1 : A_1$ and $\Delta \vdash^q e_2 : A_2$, derive
$\Delta \vdash^q (e_1, e_2) : A_1 \times A_2$. -/
def giralfPair {Delta A₁ A₂ : CompType} {q : Nat}
    (e₁ : GiralfSemJudgment Delta A₁ q)
    (e₂ : GiralfSemJudgment Delta A₂ q) :
    GiralfSemJudgment Delta (ProdComp A₁ A₂) q where
  hom_top := {
    fn := fun d => (e₁.hom_top.fn d, e₂.hom_top.fn d)
    map_charge := fun c d => Prod.ext (e₁.hom_top.map_charge c d) (e₂.hom_top.map_charge c d)
    mono := fun h => ⟨e₁.hom_top.mono h, e₂.hom_top.mono h⟩
  }
  hom_abs := {
    fn := fun d => (e₁.hom_abs.fn d, e₂.hom_abs.fn d)
    map_charge := fun c d => Prod.ext (e₁.hom_abs.map_charge c d) (e₂.hom_abs.map_charge c d)
    mono := fun h => ⟨e₁.hom_abs.mono h, e₂.hom_abs.mono h⟩
  }
  lax_comm := fun d => ⟨e₁.lax_comm d, e₂.lax_comm d⟩

/-- **Section 5.1.1 (Lazy Product First Projection in Giralf):**
From $\Delta \vdash^q e : A_1 \times A_2$, derive $\Delta \vdash^q \mathsf{proj}_1\,e : A_1$. -/
def giralfProj1 {Delta A₁ A₂ : CompType} {q : Nat}
    (e : GiralfSemJudgment Delta (ProdComp A₁ A₂) q) :
    GiralfSemJudgment Delta A₁ q where
  hom_top := {
    fn := fun d => (e.hom_top.fn d).1
    map_charge := fun c d => congrArg Prod.fst (e.hom_top.map_charge c d)
    mono := fun h => (e.hom_top.mono h).1
  }
  hom_abs := {
    fn := fun d => (e.hom_abs.fn d).1
    map_charge := fun c d => congrArg Prod.fst (e.hom_abs.map_charge c d)
    mono := fun h => (e.hom_abs.mono h).1
  }
  lax_comm := fun d => (e.lax_comm d).1

/-- **Section 5.1.1 (Lazy Product Second Projection in Giralf):**
From $\Delta \vdash^q e : A_1 \times A_2$, derive $\Delta \vdash^q \mathsf{proj}_2\,e : A_2$. -/
def giralfProj2 {Delta A₁ A₂ : CompType} {q : Nat}
    (e : GiralfSemJudgment Delta (ProdComp A₁ A₂) q) :
    GiralfSemJudgment Delta A₂ q where
  hom_top := {
    fn := fun d => (e.hom_top.fn d).2
    map_charge := fun c d => congrArg Prod.snd (e.hom_top.map_charge c d)
    mono := fun h => (e.hom_top.mono h).2
  }
  hom_abs := {
    fn := fun d => (e.hom_abs.fn d).2
    map_charge := fun c d => congrArg Prod.snd (e.hom_abs.map_charge c d)
    mono := fun h => (e.hom_abs.mono h).2
  }
  lax_comm := fun d => (e.lax_comm d).2

/-- **Section 5.1.2 (Debit Introduction `get⟨p⟩(e)` in Giralf):**
From $q' \ge p + q$ and $\Delta \vdash^{q'} e : A$, derive
$\Delta \vdash^q \mathsf{get}\langle p \rangle(e) : \triangleleft^p A$. -/
def giralfGet {Delta A : CompType} {q p q' : Nat} (h : q' ≤ p + q)
    (e : GiralfSemJudgment Delta A q') :
    GiralfSemJudgment Delta (DebitComp p A) q where
  hom_top := {
    fn := fun (d : Delta.top.carrier) =>
      ⟨(e.hom_top.fn d, e.hom_abs.fn (Delta.abs.charge q (Delta.alpha.fn d))), by
        have h₁ : A.abs.le (A.alpha.fn (e.hom_top.fn d))
            (e.hom_abs.fn (Delta.abs.charge q' (Delta.alpha.fn d))) := e.lax_comm d
        have h₂ : A.abs.le
            (e.hom_abs.fn (Delta.abs.charge q' (Delta.alpha.fn d)))
            (e.hom_abs.fn (Delta.abs.charge (p + q) (Delta.alpha.fn d))) :=
          e.hom_abs.mono (Delta.abs.charge_mono_cost (Delta.alpha.fn d) h)
        have h₃ : e.hom_abs.fn (Delta.abs.charge (p + q) (Delta.alpha.fn d)) =
            A.abs.charge p (e.hom_abs.fn (Delta.abs.charge q (Delta.alpha.fn d))) := by
          calc e.hom_abs.fn (Delta.abs.charge (p + q) (Delta.alpha.fn d))
            _ = e.hom_abs.fn (Delta.abs.charge p (Delta.abs.charge q (Delta.alpha.fn d))) :=
              congrArg e.hom_abs.fn (Delta.abs.charge_add p q (Delta.alpha.fn d))
            _ = A.abs.charge p (e.hom_abs.fn (Delta.abs.charge q (Delta.alpha.fn d))) :=
              e.hom_abs.map_charge p (Delta.abs.charge q (Delta.alpha.fn d))
        rw [h₃] at h₂
        exact A.abs.le_trans h₁ h₂⟩
    map_charge := fun c (d : Delta.top.carrier) => by
      apply Subtype.ext
      apply Prod.ext
      · exact e.hom_top.map_charge c d
      · calc e.hom_abs.fn (Delta.abs.charge q (Delta.alpha.fn (Delta.top.charge c d)))
          _ = e.hom_abs.fn (Delta.abs.charge q (Delta.abs.charge c (Delta.alpha.fn d))) :=
            congrArg (fun x => e.hom_abs.fn (Delta.abs.charge q x)) (Delta.alpha.map_charge c d)
          _ = e.hom_abs.fn (Delta.abs.charge (q + c) (Delta.alpha.fn d)) :=
            congrArg e.hom_abs.fn (Delta.abs.charge_add q c (Delta.alpha.fn d)).symm
          _ = e.hom_abs.fn (Delta.abs.charge (c + q) (Delta.alpha.fn d)) := by
            rw [Nat.add_comm q c]
          _ = e.hom_abs.fn (Delta.abs.charge c (Delta.abs.charge q (Delta.alpha.fn d))) :=
            congrArg e.hom_abs.fn (Delta.abs.charge_add c q (Delta.alpha.fn d))
          _ = A.abs.charge c (e.hom_abs.fn (Delta.abs.charge q (Delta.alpha.fn d))) :=
            e.hom_abs.map_charge c (Delta.abs.charge q (Delta.alpha.fn d))
    mono := fun h_le =>
      ⟨e.hom_top.mono h_le,
       e.hom_abs.mono (Delta.abs.charge_mono_val q (Delta.alpha.mono h_le))⟩
  }
  hom_abs := e.hom_abs
  lax_comm := fun _ => A.abs.le_refl _

/-- **Section 5.1.2 (Debit Elimination `pay(e)` in Giralf):**
From $q \ge p + q'$ and $\Delta \vdash^{q'} e : \triangleleft^p A$, derive
$\Delta \vdash^q \mathsf{pay}(e) : A$ using the counit of $\triangleright^p \dashv \triangleleft^p$. -/
def giralfPay {Delta A : CompType} {q p q' : Nat} (h : p + q' ≤ q)
    (e : GiralfSemJudgment Delta (DebitComp p A) q') :
    GiralfSemJudgment Delta A q :=
  (creditDebitCounit p A).comp (giralfStore h e)

/-! ## §5.2 Positive AARA Type Grammar and Potential Function Semantics (Figure 2) -/

/-- **Section 5.2 & Figure 2 (Positive AARA Type Grammar):**
Inductively-defined subset of computation types in Calf and Giralf:
$$A, B ::= FX \mid \top \mid A \otimes B \mid A + B \mid \triangleright^p A \mid \mathsf{CList}^p_1 A \mid \mathsf{CList}^{(p_1, p_2)}_2 A.$$ -/
inductive AARAType : Type 1 where
  | free (X : Type) : AARAType
  | top : AARAType
  | tensor (A B : AARAType) : AARAType
  | sum (A B : AARAType) : AARAType
  | credit (p : Nat) (A : AARAType) : AARAType
  | clist1 (p : Nat) (A : AARAType) : AARAType
  | clist2 (p₁ p₂ : Nat) (A : AARAType) : AARAType

/-- **Figure 2 (Underlying Value Set $\llbracket A \rrbracket : \mathcal{V}$ of an AARA Type):**
Assigns to each positive AARA type $A$ its underlying type of values $\llbracket A \rrbracket$. -/
def aaraValues : AARAType → Type
  | .free X => X
  | .top => PUnit
  | .tensor A B => aaraValues A × aaraValues B
  | .sum A B => Sum (aaraValues A) (aaraValues B)
  | .credit _ A => aaraValues A
  | .clist1 _ A => List (aaraValues A)
  | .clist2 _ _ A => List (aaraValues A)

/-- Sum of element potentials $\sum_{a \in l} \Phi(a)$ over a list $l$. -/
def listPotentialSum {α : Type} (phi : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => phi x + listPotentialSum phi xs

/-- **Figure 2 (Potential Function $\Phi_A : \llbracket A \rrbracket \to \mathbb{N}$ of an AARA Type):**
Computes the potential/credits contained within a value of type $A$. -/
def aaraPotential : (A : AARAType) → aaraValues A → Nat
  | .free _, _ => 0
  | .top, _ => 0
  | .tensor A B, (a, b) => aaraPotential A a + aaraPotential B b
  | .sum A B, s =>
      match s with
      | .inl a => aaraPotential A a
      | .inr b => aaraPotential B b
  | .credit p A, a => p + aaraPotential A a
  | .clist1 p A, l => l.length * p + listPotentialSum (aaraPotential A) l
  | .clist2 p₁ p₂ A, l =>
      l.length * p₁ + binom2 l.length * p₂ + listPotentialSum (aaraPotential A) l

/-- Sum of element potentials along an inductive quadratic-credit list `CList2Ind`. -/
def clist2ElemPotentialSum {α : Type} (phi : α → Nat) :
    {c₁ c₂ : Nat} → CList2Ind α c₁ c₂ → Nat
  | _, _, .nil => 0
  | _, _, .cons x tail => phi x + clist2ElemPotentialSum phi tail

/-- Inductive potential of a `CList2Ind α p₁ p₂` structure: the sum of its inductively-shifted
structural credits (`CList2Ind.credits`) and the potentials of its elements. -/
def clist2IndTotalPotential {α : Type} (phi : α → Nat) {p₁ p₂ : Nat}
    (t : CList2Ind α p₁ p₂) : Nat :=
  t.credits + clist2ElemPotentialSum phi t

/-- Compositional Calf computation type interpretation of a positive AARA type (Theorem 5.7):
interprets `.free X` as `FreeComp X`, `.top` as `TopComp`, `.credit p A` via the banker's credit
operator `CreditComp p`, `.tensor` and `.sum` via product/coproduct of potential-carrying types,
`.clist1` via linear-credit lists, and `.clist2 p₁ p₂ A` via the inductive family
`CList2Ind (aaraValues A) p₁ p₂` equipped with its inductive credit accumulator
`clist2IndTotalPotential`. -/
def interpAARAType : AARAType → CompType
  | .free X => FreeComp X
  | .top => TopComp
  | .tensor A B =>
      PotentialType (aaraValues A × aaraValues B)
        (fun p => aaraPotential A p.1 + aaraPotential B p.2)
  | .sum A B =>
      SumComp (interpAARAType A) (interpAARAType B)
  | .credit p A =>
      CreditComp p (interpAARAType A)
  | .clist1 p A =>
      PotentialType (List (aaraValues A))
        (fun l => l.length * p + listPotentialSum (aaraPotential A) l)
  | .clist2 p₁ p₂ A =>
      PotentialType (CList2Ind (aaraValues A) p₁ p₂)
        (clist2IndTotalPotential (aaraPotential A))

/-! ## §5.1 & §5.3 Insertion Sort (`insert` and `isort`, Examples 5.2, 5.3, and 5.18) -/

/-- **Example 5.2 (Concrete Cost-Instrumented `insert`):**
Inserts `x : Nat` into a list `l : List Nat`, incurring $1$ unit of cost for each comparison
`x ≤ y`. If `x ≤ y`, it stops immediately without recursing on the tail (as captured by the
credit-aware paramorphism of Lemma 5.1). -/
def insertCostTop (x : Nat) : List Nat → (FreeCostAlg (List Nat)).carrier
  | [] => (0, [x])
  | y :: ys =>
      if x ≤ y then
        (1, x :: y :: ys)
      else
        let recRes := insertCostTop x ys
        (1 + recRes.1, y :: recRes.2)

/-- Pure mathematical specification of `insert` (zero abstract cost). -/
def insertPure (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x ≤ y then
        x :: y :: ys
      else
        y :: insertPure x ys

/-- **Example 5.3 & Example 5.18 (Concrete Cost-Instrumented `isort`):**
Insertion sort iterating `insertCostTop` over the input list, accumulating total comparison cost. -/
def isortCostTop : List Nat → (FreeCostAlg (List Nat)).carrier
  | [] => (0, [])
  | x :: xs =>
      let tailRes := isortCostTop xs
      let insRes := insertCostTop x tailRes.2
      (tailRes.1 + insRes.1, insRes.2)

/-- Pure mathematical specification of `isort` (zero abstract cost). -/
def isortPure : List Nat → List Nat
  | [] => []
  | x :: xs => insertPure x (isortPure xs)

/-- Concrete cost-algebra homomorphism for `insert x` on $F(\mathsf{List}\,\mathbb{N})$. -/
def insertTopHom (x : Nat) : CostHom (FreeCostAlg (List Nat)) (FreeCostAlg (List Nat)) where
  fn := fun p =>
    let res := insertCostTop x p.2
    (p.1 + res.1, res.2)
  map_charge := fun c ⟨c₀, l⟩ =>
    Prod.ext (Nat.add_assoc c c₀ (insertCostTop x l).1) rfl
  mono := fun ⟨h, e⟩ => ⟨by rw [e]; exact Nat.add_le_add_right h _, by rw [e]⟩

/-- Abstract zero-cost homomorphism for `insert x` on $F(\mathsf{List}\,\mathbb{N})$. -/
def insertAbsHom (x : Nat) : CostHom (FreeCostAlg (List Nat)) (FreeCostAlg (List Nat)) where
  fn := fun p => (p.1, insertPure x p.2)
  map_charge := fun _ _ => rfl
  mono := fun ⟨h, e⟩ => ⟨h, congrArg (insertPure x) e⟩

/-- Concrete cost-algebra homomorphism for `isort` on $F(\mathsf{List}\,\mathbb{N})$. -/
def isortTopHom : CostHom (FreeCostAlg (List Nat)) (FreeCostAlg (List Nat)) where
  fn := fun p =>
    let res := isortCostTop p.2
    (p.1 + res.1, res.2)
  map_charge := fun c ⟨c₀, l⟩ =>
    Prod.ext (Nat.add_assoc c c₀ (isortCostTop l).1) rfl
  mono := fun ⟨h, e⟩ => ⟨by rw [e]; exact Nat.add_le_add_right h _, by rw [e]⟩

/-- Abstract zero-cost homomorphism for `isort` on $F(\mathsf{List}\,\mathbb{N})$. -/
def isortAbsHom : CostHom (FreeCostAlg (List Nat)) (FreeCostAlg (List Nat)) where
  fn := fun p => (p.1, isortPure p.2)
  map_charge := fun _ _ => rfl
  mono := fun ⟨h, e⟩ => ⟨h, congrArg isortPure e⟩

/-! ## §5.3 Cost Inference and Skeletal Credit Annotations (Definition 5.9, Lemmas 5.15–5.16) -/

/-- A single-world cost algebra homomorphism $f : FX \multimap FY$ is *cost-erased* (incurs zero
abstract cost) if it preserves the cost counter unchanged on every input $(c, x)$. -/
def IsZeroCostFreeHom {X Y : Type} (f : CostHom (FreeCostAlg X) (FreeCostAlg Y)) : Prop :=
  ∀ (c : Nat) (x : X), (f.fn (c, x)).1 = c

/-- **Definition 5.9 (Cost Inference for a Calf Program):**
Given concrete and abstract value types $X, Y$, a concrete cost-instrumented homomorphism
$e_\top : FX \multimap FY$, and its cost erasure $e_{\mathsf{abs}} : FX \multimap FY$, a Giralf
judgment $a : \underline{A} \vdash^q \underline{e} : \underline{B}$ is a valid *cost inference* if:
1. ($\neg\mathsf{abs}$ concrete fidelity): $\underline{A}_\top = FX$, $\underline{B}_\top = FY$, and
   $\underline{e}_\top = e_\top$;
2. ($\mathsf{abs}$ cost erasure): $\underline{A}_{\mathsf{abs}} = FX$,
   $\underline{B}_{\mathsf{abs}} = FY$, and $\underline{e}_{\mathsf{abs}} = e_{\mathsf{abs}}$ is
   the zero-cost erasure of $e_\top$. -/
structure CostInferenceCertificate {X Y : Type}
    (e_top e_abs : CostHom (FreeCostAlg X) (FreeCostAlg Y)) where
  A_inf : CompType
  B_inf : CompType
  q : Nat
  e_inf : GiralfSemJudgment A_inf B_inf q
  hA_top : A_inf.top = FreeCostAlg X
  hB_top : B_inf.top = FreeCostAlg Y
  hA_abs : A_inf.abs = FreeCostAlg X
  hB_abs : B_inf.abs = FreeCostAlg Y
  he_top : HEq e_inf.hom_top e_top
  he_abs : HEq e_inf.hom_abs e_abs
  h_erased : IsZeroCostFreeHom e_abs

/-- **Section 5.3.1 (Grammar of Skeletal Types for Cost Inference):**
$$S ::= \top \mid S_1 + S_2 \mid S_1 \times S_2 \mid \mathsf{List}(FX).$$ -/
inductive SkelType : Type 1 where
  | top : SkelType
  | sum (S₁ S₂ : SkelType) : SkelType
  | prod (S₁ S₂ : SkelType) : SkelType
  | list (X : Type) : SkelType

/-- Numeric assignment of credit and debit annotations to a skeletal type $S$ (§5.3.1):
- $\underline{\top} = \top$ (no numeric unknowns),
- $\underline{A_1 + A_2} = \triangleright^{q_1} \underline{A_1} + \triangleright^{q_2} \underline{A_2}$,
- $\underline{A_1 \times A_2} = \triangleleft^{q_1} \underline{A_1} \times \triangleleft^{q_2} \underline{A_2}$,
- $\underline{\mathsf{List}(FX)} = \mathsf{CList}^{(p_1, p_2)}_2(FX)$. -/
def SkelAnnotation : SkelType → Type
  | .top => PUnit
  | .sum S₁ S₂ => (Nat × Nat) × SkelAnnotation S₁ × SkelAnnotation S₂
  | .prod S₁ S₂ => (Nat × Nat) × SkelAnnotation S₁ × SkelAnnotation S₂
  | .list _ => Nat × Nat

/-- Pointwise addition $A_1 \oplus A_2$ of numeric credit assignments on the same skeletal type $S$
(Lemmas 5.15 & 5.16). -/
def SkelAnnotation.add : {S : SkelType} → SkelAnnotation S → SkelAnnotation S → SkelAnnotation S
  | .top, .unit, .unit => .unit
  | .sum _ _, ((q₁, q₂), a₁, a₂), ((r₁, r₂), b₁, b₂) =>
      ((q₁ + r₁, q₂ + r₂), SkelAnnotation.add a₁ b₁, SkelAnnotation.add a₂ b₂)
  | .prod _ _, ((q₁, q₂), a₁, a₂), ((r₁, r₂), b₁, b₂) =>
      ((q₁ + r₁, q₂ + r₂), SkelAnnotation.add a₁ b₁, SkelAnnotation.add a₂ b₂)
  | .list _, (p₁, p₂), (q₁, q₂) => (p₁ + q₁, p₂ + q₂)

/-- Pointwise scalar multiplication $k \odot A$ of numeric credit assignments on a skeletal type $S$
(Lemma 5.15). -/
def SkelAnnotation.smul (k : Nat) : {S : SkelType} → SkelAnnotation S → SkelAnnotation S
  | .top, .unit => .unit
  | .sum _ _, ((q₁, q₂), a₁, a₂) =>
      ((k * q₁, k * q₂), SkelAnnotation.smul k a₁, SkelAnnotation.smul k a₂)
  | .prod _ _, ((q₁, q₂), a₁, a₂) =>
      ((k * q₁, k * q₂), SkelAnnotation.smul k a₁, SkelAnnotation.smul k a₂)
  | .list _, (p₁, p₂) => (k * p₁, k * p₂)

/-- **Examples 5.13, 5.14, and 5.17 & Lemmas 5.15–5.16 (List Recursor Typing Annotation):**
Represents a credit assignment
$l : \mathsf{CList}^{(in_1, in_2)}_2(F\mathbb{N}) \vdash^q e : \P \rightharpoonup \triangleleft^d \mathsf{CList}^{(out_1, out_2)}_2(F\mathbb{N})$
on a skeletal list recursor such as $\underline{\mathsf{snoc'}}$. -/
structure ListRecAnnotation where
  in_lin : Nat
  in_quad : Nat
  ctx_q : Nat
  debit : Nat
  out_lin : Nat
  out_quad : Nat
  deriving DecidableEq, Repr

/-- Pointwise addition $A_1 \oplus A_2$ of `ListRecAnnotation`s (Lemmas 5.15 & 5.16). -/
def ListRecAnnotation.add (A₁ A₂ : ListRecAnnotation) : ListRecAnnotation where
  in_lin := A₁.in_lin + A₂.in_lin
  in_quad := A₁.in_quad + A₂.in_quad
  ctx_q := A₁.ctx_q + A₂.ctx_q
  debit := A₁.debit + A₂.debit
  out_lin := A₁.out_lin + A₂.out_lin
  out_quad := A₁.out_quad + A₂.out_quad

/-- Pointwise scalar multiplication $k \odot A$ of a `ListRecAnnotation` (Lemma 5.15). -/
def ListRecAnnotation.smul (k : Nat) (A : ListRecAnnotation) : ListRecAnnotation where
  in_lin := k * A.in_lin
  in_quad := k * A.in_quad
  ctx_q := k * A.ctx_q
  debit := k * A.debit
  out_lin := k * A.out_lin
  out_quad := k * A.out_quad

/-- Semantic validity predicate for a `ListRecAnnotation` on a list transformation that increases
list length by $1$ (`|l'| = |l| + 1`, as in `snoc'`) and incurs `stepCost` units of cost per input
element (`stepCost = 1` for cost-aware $\underline{\mathsf{snoc'}}$ and `stepCost = 0` for cost-free
$\underline{\widehat{\mathsf{snoc'}}}$):
for every input list length $n = |l|$, the total credits spent ($n \cdot \mathsf{stepCost}$) plus
the output list's potential ($(n + 1) \cdot out_1 + \binom{n + 1}{2} \cdot out_2$) is bounded by
the input list's potential ($n \cdot in_1 + \binom{n}{2} \cdot in_2$) plus the top-level credit
context $q$ and the assumed debit $d$. -/
def ValidSnocRecAnnotation (stepCost : Nat) (A : ListRecAnnotation) : Prop :=
  ∀ n : Nat,
    n * stepCost + ((n + 1) * A.out_lin + binom2 (n + 1) * A.out_quad) ≤
      (n * A.in_lin + binom2 n * A.in_quad) + A.ctx_q + A.debit

/-- **Example 5.14(1):** Cost-aware annotation $A_{\mathrm{ca}}$ for $\underline{\mathsf{snoc'}}$:
$l : \mathsf{CList}^{(1, 0)}_2(F\mathbb{N}) \vdash^0 \underline{\mathsf{snoc'}} :
\P \rightharpoonup \triangleleft^0 \mathsf{CList}^{(0, 0)}_2(F\mathbb{N})$. -/
def snocAnnCA : ListRecAnnotation :=
  ⟨1, 0, 0, 0, 0, 0⟩

/-- **Example 5.14(2):** First cost-free annotation $A_{\mathrm{cf1}}$ for $\underline{\widehat{\mathsf{snoc'}}}$
(movement of linear credits):
$l : \mathsf{CList}^{(1, 0)}_2(F\mathbb{N}) \vdash^0 \underline{\widehat{\mathsf{snoc'}}} :
\P \rightharpoonup \triangleleft^1 \mathsf{CList}^{(1, 0)}_2(F\mathbb{N})$. -/
def snocAnnCF1 : ListRecAnnotation :=
  ⟨1, 0, 0, 1, 1, 0⟩

/-- **Example 5.14(3):** Second cost-free annotation $A_{\mathrm{cf2}}$ for $\underline{\widehat{\mathsf{snoc'}}}$
(movement of quadratic credits):
$l : \mathsf{CList}^{(1, 1)}_2(F\mathbb{N}) \vdash^0 \underline{\widehat{\mathsf{snoc'}}} :
\P \rightharpoonup \triangleleft^0 \mathsf{CList}^{(0, 1)}_2(F\mathbb{N})$. -/
def snocAnnCF2 : ListRecAnnotation :=
  ⟨1, 1, 0, 0, 0, 1⟩

/-- **Example 5.17:** Symbolic linear combination
$A_{\mathrm{ca}} \oplus (p_1 \odot A_{\mathrm{cf1}}) \oplus (p_2 \odot A_{\mathrm{cf2}})$ yielding
the resource-polymorphic typing for $\underline{\mathsf{snoc'}}$. -/
def snocSymbolicAnnotation (p₁ p₂ : Nat) : ListRecAnnotation :=
  ListRecAnnotation.add
    (ListRecAnnotation.add snocAnnCA (ListRecAnnotation.smul p₁ snocAnnCF1))
    (ListRecAnnotation.smul p₂ snocAnnCF2)

end Grodin2026


