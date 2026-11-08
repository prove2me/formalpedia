-- Prove2me | Definitions.Def_Grodin2026_Banker
-- name    : Grodin2026_Banker
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T17:17:27.429958+00:00
-- url     : https://prove2.me/theorems/73a97e84-c6f3-4748-bbe9-46eb0696edc4
-- title:
--   Section 4: The Banker's View — Credit and Debit Operators, Dependent Copowers, and Credit-Carrying Lists
-- statement:
--   Formalizes Section 4 of Grodin, Chu, Li, Hoffmann & Harper (2026): the credit operator `CreditComp` ($\triangleright^c A \coloneqq \mathsf{Abstraction}(\mathsf{charge}_A\langle c \rangle : A \multimap A)$, Definition 4.1), credit weakening `creditWeaken` (Lemma 4.5), `saveComp` ($\mathsf{save}\langle c \rangle : A \multimap \triangleright^c A$) and `spendComp` ($\mathsf{spend}\langle c \rangle : \triangleright^c A \multimap A$, Definition 4.7), dependent copowers `DepCopowerComp` and banker's potential `BankerPotentialComp` ($(x : X) \ltimes \triangleright^{\Phi(x)} \top$, Lemma 4.10), the debit operator `DebitComp` ($\triangleleft^c A \coloneqq \triangleright^c \top \mathrel{\multimap\!\!\!\!+} A$, Definition 4.11) with unit `creditDebitUnit` and counit `creditDebitCounit` (Lemma 4.12), linear-credit lists `CList1Comp` ($\mathsf{CList}^c_1(FX)$, Definition 4.13) with pre-paid `revAppendTop` and `reverseCList1Top` (Example 4.15), and the shifting-index inductive family `CList2Ind` and `CList2Comp` ($\mathsf{CList}^{(c_1, c_2)}_2(FX)$, Definition 4.18).
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Section 4, pp. 14-16.

import Definitions.Def_Grodin2026_Physicist

/-!
# The Banker's View: Credits, Debits, and Credit-Carrying Lists (Grodin et al., 2026, §4)

Constructive Lean 4 formalization of Section 4 of:
Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper (2026),
*Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost*
(`arXiv:2607.08547v2`).

This module formalizes:
- **§4.1:** The credit operator $\triangleright^c A := \mathsf{Abstraction}(\mathsf{charge}_A\langle c \rangle : A \multimap A)$
  (Definition 4.1, Remarks 4.2–4.3), ghost-data modal invariance (Lemma 4.4), credit weakening
  $\triangleright^{c'} A \mathrel{\multimap\!\!\!\!+} \triangleright^c A$ for $c' \ge c$ (Lemma 4.5),
  monoidal laws $\triangleright^0 A = A$ and $\triangleright^{c_1 + c_2} A = \triangleright^{c_1} \triangleright^{c_2} A$
  (Lemma 4.6), $\mathsf{save}\langle c \rangle : A \multimap \triangleright^c A$ and
  $\mathsf{spend}\langle c \rangle : \triangleright^c A \multimap A$ (Definition 4.7),
  $\mathsf{spend}\langle c \rangle \circ \mathsf{save}\langle c \rangle = \mathsf{charge}_A\langle c \rangle$
  (Lemma 4.8), the dependent copower decomposition
  $\mathsf{Potential}(\Phi : X \to \mathbb{C}) = (x : X) \ltimes \triangleright^{\Phi(x)} \top$
  (Lemma 4.10), the debit operator $\triangleleft^c A := \triangleright^c \top \mathrel{\multimap\!\!\!\!+} A$
  (Definition 4.11), and the credit–debit adjunction $\triangleright^c \dashv \triangleleft^c$
  (Lemma 4.12).
- **§4.2:** Linear-credit lists $\mathsf{CList}^c_1 A := \mathsf{List}(\triangleright^c A)$
  (Definition 4.13, Corollary 4.14), linear-time pre-paid `revAppend` and `reverse`
  (Example 4.15), the banker's batched queue (Example 4.16), and the inductive family of
  quadratic-credit lists $\mathsf{CList}^{(c_1, c_2)}_2 A$ carrying $c_1 n + c_2 \binom{n}{2}$
  credits (Definition 4.18, Corollary 4.19).
-/

namespace Grodin2026

/-! ## §4.1 The Credit Operator $\triangleright^c A$, `save⟨c⟩`, and `spend⟨c⟩` -/

/-- **Remark 4.2:** The cost effect $\mathsf{charge}_A\langle c \rangle : A \multimap A$ lifts to a
computation homomorphism on any phased computation type $A : \mathcal{C}$ because $\alpha_A$ is a
cost algebra homomorphism and $(\mathbb{N}, 0, +)$ is commutative. -/
def chargeCompHom (A : CompType) (c : Nat) : CompHom A A where
  hom_top := chargeCostHom A.top c
  hom_abs := chargeCostHom A.abs c
  comm := fun a => A.alpha.map_charge c a

/-- **Definition 4.1 & Remark 4.3 (The Credit Operator $\triangleright^c A$):**
Annotates a computation type $A : \mathcal{C}$ with $c$ additional credits by constructing
$\triangleright^c A := \mathsf{Abstraction}(\mathsf{charge}_A\langle c \rangle : A \multimap A)$,
which increases the cost emitted by $\alpha_A$ by $c$ units. -/
def CreditComp (c : Nat) (A : CompType) : CompType :=
  AbstractionCompLayered A A (chargeCompHom A c)

/-- Functorial action of $\triangleright^c$ on strict computation homomorphisms
$f : A \multimap B$. -/
def CreditComp.map (c : Nat) {A B : CompType} (f : CompHom A B) :
    CompHom (CreditComp c A) (CreditComp c B) where
  hom_top := f.hom_top
  hom_abs := f.hom_abs
  comm := fun a => by
    change B.abs.charge c (B.alpha.fn (f.hom_top.fn a)) =
      f.hom_abs.fn (A.abs.charge c (A.alpha.fn a))
    rw [f.comm a, f.hom_abs.map_charge c (A.alpha.fn a)]

/-- Functorial action of $\triangleright^c$ on lax computation homomorphisms
$f : A \mathrel{\multimap\!\!\!\!+} B$. -/
def CreditComp.mapLax (c : Nat) {A B : CompType} (f : LaxCompHom A B) :
    LaxCompHom (CreditComp c A) (CreditComp c B) where
  hom_top := f.hom_top
  hom_abs := f.hom_abs
  lax_comm := fun a => by
    change B.abs.le (B.abs.charge c (B.alpha.fn (f.hom_top.fn a)))
      (f.hom_abs.fn (A.abs.charge c (A.alpha.fn a)))
    rw [f.hom_abs.map_charge c (A.alpha.fn a)]
    exact B.abs.charge_mono_val c (f.lax_comm a)

/-- **Lemma 4.5 (Credit Weakening Map):**
For $c \le c'$, the credit operator admits a lax homomorphism
$\triangleright^{c'} A \mathrel{\multimap\!\!\!\!+} \triangleright^c A$ that wastes $c' - c$ credits. -/
def creditWeaken (c' c : Nat) (h : c ≤ c') (A : CompType) :
    LaxCompHom (CreditComp c' A) (CreditComp c A) where
  hom_top := CostHom.id A.top
  hom_abs := CostHom.id A.abs
  lax_comm := fun a => A.abs.charge_mono_cost (A.alpha.fn a) h

/-- **Definition 4.7 (`save⟨c⟩` Operation):**
$\mathsf{save}\langle c \rangle : A \multimap \triangleright^c A$ incurs no concrete cost (`id` on $A_\top$)
and reports $c$ units of abstract cost (`charge⟨c⟩` on $A_{\mathsf{abs}}$), Constructed via
Corollary 2.23(1) from $f_\top = \mathrm{id}_A$. -/
def saveComp (c : Nat) (A : CompType) : CompHom A (CreditComp c A) where
  hom_top := CostHom.id A.top
  hom_abs := chargeCostHom A.abs c
  comm := fun _ => rfl

/-- **Definition 4.7 (`spend⟨c⟩` Operation):**
$\mathsf{spend}\langle c \rangle : \triangleright^c A \multimap A$ incurs $c$ units of concrete cost
(`charge⟨c⟩` on $A_\top$) and reports $0$ abstract cost (`id` on $A_{\mathsf{abs}}$), constructed via
Corollary 2.23(2) from $g_{\mathsf{abs}} = \mathrm{id}_A$. -/
def spendComp (c : Nat) (A : CompType) : CompHom (CreditComp c A) A where
  hom_top := chargeCostHom A.top c
  hom_abs := CostHom.id A.abs
  comm := fun a => A.alpha.map_charge c a

/-! ## §4.1 Dependent Copowers and Connecting Physicist's Potential to Banker's Credits -/

/-- Monoidal unit $\top := F(1)$ as a phased computation type in $\mathcal{C}$. -/
def TopComp : CompType :=
  FreeComp PUnit

/-- Dependent copower $(x : X) \ltimes A(x)$ of single-world cost algebras indexed by $x : X$:
elements are pairs $\langle x, a \rangle$ where $x : X$ and $a : U(A(x))$ with shared cost action
carried by $A(x)$. -/
def DepCopowerCostAlg (X : Type) (A : X → CostAlg) : CostAlg where
  carrier := Sigma (fun x : X => (A x).carrier)
  le := fun ⟨x₁, a₁⟩ ⟨x₂, a₂⟩ => ∃ h : x₁ = x₂, (A x₂).le (h ▸ a₁) a₂
  le_refl := fun ⟨x, a⟩ => ⟨rfl, (A x).le_refl a⟩
  le_trans := by
    rintro ⟨x₁, a₁⟩ ⟨x₂, a₂⟩ ⟨x₃, a₃⟩ ⟨h₁₂, le₁₂⟩ ⟨h₂₃, le₂₃⟩
    subst h₁₂; subst h₂₃
    exact ⟨rfl, (A x₁).le_trans le₁₂ le₂₃⟩
  charge := fun c ⟨x, a⟩ => ⟨x, (A x).charge c a⟩
  charge_zero := fun ⟨x, a⟩ => Sigma.ext rfl (heq_of_eq ((A x).charge_zero a))
  charge_add := fun c₁ c₂ ⟨x, a⟩ => Sigma.ext rfl (heq_of_eq ((A x).charge_add c₁ c₂ a))
  charge_mono_cost := fun ⟨x, a⟩ h => ⟨rfl, (A x).charge_mono_cost a h⟩
  charge_mono_val := by
    rintro c ⟨x₁, a₁⟩ ⟨x₂, a₂⟩ ⟨h₁₂, le₁₂⟩
    subst h₁₂
    exact ⟨rfl, (A x₁).charge_mono_val c le₁₂⟩

/-- Dependent copower $(x : X) \ltimes A(x)$ of phased computation types $A : X \to \mathcal{C}$
(§2, p. 4 & Lemma 4.10). -/
def DepCopowerComp (X : Type) (A : X → CompType) : CompType where
  top := DepCopowerCostAlg X (fun x => (A x).top)
  abs := DepCopowerCostAlg X (fun x => (A x).abs)
  alpha := {
    fn := fun ⟨x, a⟩ => ⟨x, (A x).alpha.fn a⟩
    map_charge := fun c ⟨x, a⟩ =>
      Sigma.ext rfl (heq_of_eq ((A x).alpha.map_charge c a))
    mono := by
      rintro ⟨x₁, a₁⟩ ⟨x₂, a₂⟩ ⟨h₁₂, le₁₂⟩
      subst h₁₂
      exact ⟨rfl, (A x₁).alpha.mono le₁₂⟩
  }

/-- Banker's representation $(x : X) \ltimes \triangleright^{\Phi(x)} \top$ of a value $x : X$
stored alongside $\Phi(x)$ credits (Lemma 4.10). -/
def BankerPotentialComp (X : Type) (Phi : X → Nat) : CompType :=
  DepCopowerComp X (fun x => CreditComp (Phi x) TopComp)

/-! ## §4.1 The Debit Operator $\triangleleft^c A$ and Credit–Debit Adjunction -/

/-- Concrete cost algebra for the debit computation type $\triangleleft^c A := \triangleright^c \top \mathrel{\multimap\!\!\!\!+} A$
(Definition 4.11):
elements are pairs $(a_\top, a_{\mathsf{abs}}) : UA_\top \times UA_{\mathsf{abs}}$ satisfying the
lax inequality $\alpha_A(a_\top) \le_{A_{\mathsf{abs}}} \mathsf{charge}_{A_{\mathsf{abs}}}\langle c \rangle(a_{\mathsf{abs}})$
expressing that $a_\top$ may use up to $c$ assumed credits relative to $a_{\mathsf{abs}}$. -/
def DebitTopCostAlg (c : Nat) (A : CompType) : CostAlg :=
  CommaCostAlg A.alpha (chargeCostHom A.abs c)

/-- **Definition 4.11 (The Debit Operator $\triangleleft^c A := \triangleright^c \top \mathrel{\multimap\!\!\!\!+} A$):**
Annotates a computation type $A : \mathcal{C}$ with an opportunity to make use of $c$ credits via
a lax homomorphism assuming $c$ credits. -/
def DebitComp (c : Nat) (A : CompType) : CompType where
  top := DebitTopCostAlg c A
  abs := A.abs
  alpha := {
    fn := fun p => p.1.2
    map_charge := fun _ _ => rfl
    mono := fun h => h.2
  }

/-- **Lemma 4.12 (Credit–Debit Adjunction Unit — Taking Out a Loan):**
The strict computation homomorphism $\eta_c : A \multimap \triangleleft^c \triangleright^c A$. -/
def creditDebitUnit (c : Nat) (A : CompType) :
    CompHom A (DebitComp c (CreditComp c A)) where
  hom_top := {
    fn := fun a => ⟨(a, A.alpha.fn a), A.abs.le_refl (A.abs.charge c (A.alpha.fn a))⟩
    map_charge := fun c' a =>
      Subtype.ext (Prod.ext rfl (A.alpha.map_charge c' a))
    mono := fun h => ⟨h, A.alpha.mono h⟩
  }
  hom_abs := CostHom.id A.abs
  comm := fun _ => rfl

/-- **Lemma 4.12 (Credit–Debit Adjunction Counit — Paying Off a Loan):**
The lax computation homomorphism $\varepsilon_c : \triangleright^c \triangleleft^c A \mathrel{\multimap\!\!\!\!+} A$. -/
def creditDebitCounit (c : Nat) (A : CompType) :
    LaxCompHom (CreditComp c (DebitComp c A)) A where
  hom_top := {
    fn := fun p => p.1.1
    map_charge := fun _ _ => rfl
    mono := fun h => h.1
  }
  hom_abs := CostHom.id A.abs
  lax_comm := fun p => p.2

/-! ## §4.2 Credit-Carrying Lists (`CList₁` and `CList₂`) -/

/-- **Definition 4.13 (Linear-Credit Lists $\mathsf{CList}^c_1(FX)$):**
Lists of elements of type $X$ in which each element is accompanied by $c$ credits, carrying total
potential $|l| \cdot c$. -/
def CList1Comp (c : Nat) (X : Type) : CompType :=
  PotentialType (List X) (fun l => l.length * c)

/-- **Example 4.15 (Concrete `revAppend` with Cost on $\mathsf{CList}^1_1(FX)$):**
Each recursive step spends $1$ unit of credit to cons the head onto the accumulator. -/
def revAppendTop {X : Type} : List X → List X → (FreeCostAlg (List X)).carrier
  | [], acc => (0, acc)
  | x :: l, acc =>
      let res := revAppendTop l (x :: acc)
      (1 + res.1, res.2)

/-- **Example 4.15 (Abstract Zero-Cost `revAppend` Specification):**
In the abstract phase, `revAppend` is zero-cost because the required credits were pre-paid in the
input type $\mathsf{CList}^1_1(FX)$. -/
def revAppendAbs {X : Type} (l acc : List X) : (FreeCostAlg (List X)).carrier :=
  retFree (l.reverseAux acc)

/-- Concrete cost-algebra homomorphism for `reverse` on $\mathsf{CList}^1_1(FX)$ (Example 4.15). -/
def reverseCList1Top {X : Type} : CostHom (FreeCostAlg (List X)) (FreeCostAlg (List X)) where
  fn := fun p =>
    let res := revAppendTop p.2 []
    (p.1 + res.1, res.2)
  map_charge := fun c ⟨c₀, l⟩ =>
    Prod.ext (Nat.add_assoc c c₀ (revAppendTop l []).1) rfl
  mono := fun ⟨h, e⟩ => ⟨by rw [e]; exact Nat.add_le_add_right h _, by rw [e]⟩

/-- Abstract zero-cost homomorphism for `reverse` on $\mathsf{CList}^1_1(FX)$ (Example 4.15). -/
def reverseCList1Abs {X : Type} : CostHom (FreeCostAlg (List X)) (FreeCostAlg (List X)) where
  fn := fun p => (p.1, p.2.reverse)
  map_charge := fun _ _ => rfl
  mono := fun ⟨h, e⟩ => ⟨h, congrArg List.reverse e⟩

/-- Binomial coefficient $\binom{n}{2} = \frac{n(n-1)}{2}$ defined by structural recursion so that
$\binom{0}{2} = 0$ and $\binom{n+1}{2} = n + \binom{n}{2}$ definitionally (§4.2, p. 16). -/
def binom2 : Nat → Nat
  | 0 => 0
  | n + 1 => n + binom2 n

/-- **Definition 4.18 (Inductive Family $\mathsf{CList}^{(c_1, c_2)}_2$ of Quadratic-Credit Lists):**
Inductive family indexed by the linear credit coefficient $c_1$ and quadratic credit coefficient $c_2$,
where `cons` shifts the linear coefficient of the tail from $c_1$ to $c_2 + c_1$:
`cons : ▷^{c₁} A ⊗ CList^{(c₂ + c₁, c₂)}_2 A ⊸ CList^{(c₁, c₂)}_2 A`. -/
inductive CList2Ind (α : Type) : Nat → Nat → Type where
  | nil {c₁ c₂ : Nat} : CList2Ind α c₁ c₂
  | cons {c₁ c₂ : Nat} (head : α) (tail : CList2Ind α (c₂ + c₁) c₂) : CList2Ind α c₁ c₂

/-- Total credits stored inside a `CList2Ind α c₁ c₂` structure according to Definition 4.18:
`nil` stores $0$ credits, and `cons` stores $c_1$ credits at the head plus the credits of the
shifted tail `CList2Ind α (c₂ + c₁) c₂`. -/
def CList2Ind.credits {α : Type} : {c₁ c₂ : Nat} → CList2Ind α c₁ c₂ → Nat
  | _, _, .nil => 0
  | c₁, _, .cons _ tail => c₁ + tail.credits

/-- Underlying list of elements of a `CList2Ind α c₁ c₂` (erasing credit indices). -/
def CList2Ind.toList {α : Type} : {c₁ c₂ : Nat} → CList2Ind α c₁ c₂ → List α
  | _, _, .nil => []
  | _, _, .cons x tail => x :: tail.toList

/-- Canonical lifting of a plain `List α` into `CList2Ind α c₁ c₂`. -/
def CList2Ind.ofList {α : Type} (c₁ c₂ : Nat) : List α → CList2Ind α c₁ c₂
  | [] => .nil
  | x :: xs => .cons x (CList2Ind.ofList (c₂ + c₁) c₂ xs)

/-- **Definition 4.18 & Corollary 4.19 (Quadratic-Credit List Computation Type $\mathsf{CList}^{(c_1, c_2)}_2(FX)$):**
Carries total potential $|l| \cdot c_1 + \binom{|l|}{2} \cdot c_2$. -/
def CList2Comp (c₁ c₂ : Nat) (X : Type) : CompType :=
  PotentialType (List X) (fun l => l.length * c₁ + binom2 l.length * c₂)

end Grodin2026


