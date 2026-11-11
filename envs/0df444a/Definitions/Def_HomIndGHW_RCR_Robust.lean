-- Prove2me | Definitions.Def_HomIndGHW_RCR_Robust
-- name    : HomIndGHW_RCR_Robust
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:01:47.061024+00:00
-- url     : https://prove2.me/theorems/6f8f67af-405e-47a9-9867-b98d772d7686
-- title:
--   Robust and pro-robust equivalence relations, stable colourings of a disjoint union, ≡⁺ and 𝔈, isomorphisms, distinguishing classes (Definitions 4.1, 4.3, 4.5; §4.3)
-- statement:
--   Let $\mathcal A,\mathcal B$ have disjoint domains. An equivalence relation $\equiv$ on $T_k(\mathcal A)\cup T_k(\mathcal B)$ is **robust** (Definition 4.1) if for $\mathcal C,\mathcal C'\in\{\mathcal A,\mathcal B\}$ and $s\in T_k(\mathcal C)$, $s'\in T_k(\mathcal C')$ with $s\equiv s'$: $(\mathrm{atp}(s),\mathrm{stp}(s,s))=(\mathrm{atp}(s'),\mathrm{stp}(s',s'))$ and
--   $$\{\!\{(\mathrm{stp}(s,t),[t]_\equiv)\mid t\in T_k(\mathcal C),\ \mathrm{stp}(s,t)\neq\emptyset\}\!\}=\{\!\{(\mathrm{stp}(s',t'),[t']_\equiv)\mid t'\in T_k(\mathcal C'),\ \mathrm{stp}(s',t')\neq\emptyset\}\!\}.$$
--   An equivalence relation $\approx$ on $\mathrm{MCT}_k(\mathcal A)\cup\mathrm{MCT}_k(\mathcal B)$ is **pro-robust** (Definition 4.3) if $(\alpha,s)\approx(\alpha',s')$ implies $\alpha=\alpha'$, $\mathrm{stp}(s,s)=\mathrm{stp}(s',s')$ and the analogous multisets over pro-tuples coincide. $\equiv_\infty$ and $\approx_\infty$ are the equivalence relations induced by the stable $k$-RCR and $k$-proRCR colourings of the union. For $\equiv$ robust, $(\alpha,s)\equiv^+(\alpha',s')$ iff $\alpha=\alpha'$ and $s\equiv s'$, and $\mathfrak E:\equiv\mapsto\equiv^+$ (p. 32). A map $\mathfrak P$ from robust to pro-robust relations is an **isomorphism** (Definition 4.5) if it is a bijection and $\equiv\subseteq\equiv'\iff\mathfrak P(\equiv)\subseteq\mathfrak P(\equiv')$. A relation **distinguishes** $\mathcal A,\mathcal B$ if some class $E$ has $|E\cap T_k(\mathcal A)|\neq|E\cap T_k(\mathcal B)|$ (resp. with $\mathrm{MCT}_k$), and $\equiv_c$ is a **coarsest robust** relation: robust and containing every robust relation (§4.3).
--
--   These notions compare $k$-RCR and $k$-proRCR without running either.
--
--   **Formalization Note.** Disjoint domains are the sum types $T_k(\mathcal A)\oplus T_k(\mathcal B)$ and $\mathrm{MCT}_k(\mathcal A)\oplus\mathrm{MCT}_k(\mathcal B)$; equivalence relations are `Setoid`s, $\subseteq$ is `≤`, classes are quotient elements. Since $\mathrm{stp}(s,t)=\emptyset$ for tuples over disjoint domains, running $k$-RCR on the union colours $t\in T_k(\mathcal C)$ by $\kappa^{\mathcal C}_i(t)$; $\equiv_\infty$ is "same colour at every round", the intersection of the refining round partitions, which is the stable partition. `plus` is $\mathfrak E$ on all setoids; that it maps robust to pro-robust relations is Proposition 4.6.
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 29, Definition 4.1; p. 30, Definition 4.3; p. 31, Definition 4.5; p. 32, construction of ≡⁺; p. 35, §4.3

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement

set_option autoImplicit false

namespace HomIndGHW.RCR

/-!
# Robust and pro-robust equivalence relations, the stable colourings on a disjoint union, `≡⁺`,
# the map `𝔈`, isomorphisms, and "distinguishes" for an equivalence relation

Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, *Homomorphism Indistinguishability Beyond
Graphs*, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), §4:
Definition 4.1 (p. 29), Definition 4.3 (p. 30), Definition 4.5 (p. 31), the construction of `≡⁺`
(p. 32), and §4.3 (p. 35).

* The two structures `A`, `B` "with disjoint domains" have domains `V`, `W`, and the union
  `T_k(A) ∪ T_k(B)` is the sum type `FT A B k = T_k(A) ⊕ T_k(B)`; likewise
  `FP A B k = MCT_k(A) ⊕ MCT_k(B)`. Disjointness is automatic.
* An equivalence relation is a Mathlib `Setoid`; `≡ ⊆ ≡′` is `≡ ≤ ≡′`; the class `[t]_≡` is the
  quotient element `⟦t⟧`.
* Running k-RCR on `T_k(A) ∪ T_k(B)`: since `stp(s, t) = ∅` whenever `s`, `t` come from different
  (disjoint) domains, the round-`i` colour of `t ∈ T_k(C)` is `κ_i^C(t)`. The stable colouring
  induces the equivalence relation "same colour at every round" (`rcrStable`): the partitions refine
  round by round and, once two consecutive ones coincide, all later ones do. Likewise
  `proStable` for k-proRCR.
-/

open Structure Classical

variable {σ : Sig} {V : Type*} {W : Type*}

/-- `T_k(A) ∪ T_k(B)` for structures with disjoint domains, as a sum type. -/
abbrev FT [Finite V] [Finite W] (A : Structure σ V) (B : Structure σ W) (k : ℕ) : Type _ :=
  (flatTuples A k) ⊕ (flatTuples B k)

/-- `MCT_k(A) ∪ MCT_k(B)` for structures with disjoint domains, as a sum type. -/
abbrev FP [Finite V] [Finite W] [LinearOrder σ.Sym] (A : Structure σ V) (B : Structure σ W)
    (k : ℕ) : Type _ :=
  (mct A k) ⊕ (mct B k)

section Robust

variable [Finite V] [Finite W] {A : Structure σ V} {B : Structure σ W} {k : ℕ}

/-- `(atp(s), stp(s, s))` for `s ∈ T_k(A) ∪ T_k(B)`. -/
noncomputable def ftKey0 : FT A B k → Finset σ.Sym × Finset (ℕ × ℕ)
  | .inl s => (atp A s.1, stp s.1 s.1)
  | .inr s => (atp B s.1, stp s.1 s.1)

/-- `{{(stp(s, t), [t]_≡) | t ∈ T_k(C), stp(s, t) ≠ ∅}}` for `s ∈ T_k(C)`, `C ∈ {A, B}`. -/
noncomputable def ftNbrs (S : Setoid (FT A B k)) :
    FT A B k → Multiset (Finset (ℕ × ℕ) × Quotient S)
  | .inl s => ((flatTuples A k).attach.filter fun t => stp s.1 t.1 ≠ ∅).val.map
      fun t => (stp s.1 t.1, Quotient.mk S (.inl t))
  | .inr s => ((flatTuples B k).attach.filter fun t => stp s.1 t.1 ≠ ∅).val.map
      fun t => (stp s.1 t.1, Quotient.mk S (.inr t))

/-- A **robust** equivalence relation on `T_k(A) ∪ T_k(B)` (Definition 4.1, p. 29): whenever
`s ≡ s′`, `(atp(s), stp(s, s)) = (atp(s′), stp(s′, s′))` and the multisets
`{{(stp(s, t), [t]_≡) | t ∈ T_k(C), stp(s, t) ≠ ∅}}` and
`{{(stp(s′, t′), [t′]_≡) | t′ ∈ T_k(C′), stp(s′, t′) ≠ ∅}}` coincide. -/
def Robust (S : Setoid (FT A B k)) : Prop :=
  ∀ x y : FT A B k, S.r x y → ftKey0 x = ftKey0 y ∧ ftNbrs S x = ftNbrs S y

/-- The round-`i` k-RCR colour of an element of `T_k(A) ∪ T_k(B)`. -/
noncomputable def kappaU (i : ℕ) : FT A B k → RCRCol σ i
  | .inl s => kappa A k i s.1
  | .inr s => kappa B k i s.1

/-- `≡_∞`, the equivalence relation induced by the stable k-RCR colouring of
`T_k(A) ∪ T_k(B)` (Proposition 4.2): same colour at every round. -/
def rcrStable (A : Structure σ V) (B : Structure σ W) (k : ℕ) : Setoid (FT A B k) where
  r x y := ∀ i, kappaU i x = kappaU i y
  iseqv := ⟨fun _ _ => rfl, fun h i => (h i).symm, fun h h' i => (h i).trans (h' i)⟩

/-- A robust equivalence relation `≡` **distinguishes `A`, `B`** (§4.3, p. 35) if some class `E`
has `|E ∩ T_k(A)| ≠ |E ∩ T_k(B)|`; the class is `[x]_≡`. -/
def RelDistinguishes (S : Setoid (FT A B k)) : Prop :=
  ∃ x : FT A B k,
    ((flatTuples A k).attach.filter fun t => S.r x (.inl t)).card ≠
      ((flatTuples B k).attach.filter fun t => S.r x (.inr t)).card

/-- `≡_c` is **a coarsest robust equivalence relation** (§4.3, p. 35): it is robust and every
robust equivalence relation is contained in it. -/
def IsCoarsestRobust (S : Setoid (FT A B k)) : Prop :=
  Robust S ∧ ∀ S' : Setoid (FT A B k), Robust S' → S' ≤ S

end Robust

section ProRobust

variable [Finite V] [Finite W] [LinearOrder σ.Sym] {A : Structure σ V} {B : Structure σ W}
  {k : ℕ}

/-- `(α, stp(s, s))` for a pro-tuple `(α, s)`. -/
noncomputable def fpKey0 : FP A B k → List σ.Sym × Finset (ℕ × ℕ)
  | .inl p => (p.1.1, stp p.1.2 p.1.2)
  | .inr p => (p.1.1, stp p.1.2 p.1.2)

/-- `{{(stp(s, t), [(β, t)]_≈) | (β, t) ∈ MCT_k(C), stp(s, t) ≠ ∅}}` for `(α, s) ∈ MCT_k(C)`. -/
noncomputable def fpNbrs (S : Setoid (FP A B k)) :
    FP A B k → Multiset (Finset (ℕ × ℕ) × Quotient S)
  | .inl p => ((mct A k).attach.filter fun q => stp p.1.2 q.1.2 ≠ ∅).val.map
      fun q => (stp p.1.2 q.1.2, Quotient.mk S (.inl q))
  | .inr p => ((mct B k).attach.filter fun q => stp p.1.2 q.1.2 ≠ ∅).val.map
      fun q => (stp p.1.2 q.1.2, Quotient.mk S (.inr q))

/-- A **pro-robust** equivalence relation on `MCT_k(A) ∪ MCT_k(B)` (Definition 4.3, p. 30):
whenever `(α, s) ≈ (α′, s′)`, `α = α′`, `stp(s, s) = stp(s′, s′)`, and the multisets
`{{(stp(s, t), [(β, t)]_≈) | (β, t) ∈ MCT_k(C), stp(s, t) ≠ ∅}}` and
`{{(stp(s′, t′), [(β′, t′)]_≈) | (β′, t′) ∈ MCT_k(C′), stp(s′, t′) ≠ ∅}}` coincide. -/
def ProRobust (S : Setoid (FP A B k)) : Prop :=
  ∀ x y : FP A B k, S.r x y → fpKey0 x = fpKey0 y ∧ fpNbrs S x = fpNbrs S y

/-- The round-`i` k-proRCR colour of an element of `MCT_k(A) ∪ MCT_k(B)`. -/
noncomputable def chiU (i : ℕ) : FP A B k → ProCol σ i
  | .inl p => chi A k i p.1
  | .inr p => chi B k i p.1

/-- `≈_∞`, the equivalence relation induced by the stable k-proRCR colouring of
`MCT_k(A) ∪ MCT_k(B)` (Proposition 4.4): same colour at every round. -/
def proStable (A : Structure σ V) (B : Structure σ W) (k : ℕ) : Setoid (FP A B k) where
  r x y := ∀ i, chiU i x = chiU i y
  iseqv := ⟨fun _ _ => rfl, fun h i => (h i).symm, fun h h' i => (h i).trans (h' i)⟩

/-- A pro-robust equivalence relation `≈` **distinguishes `A`, `B`** (§4.3, p. 35) if some class
`E` has `|E ∩ MCT_k(A)| ≠ |E ∩ MCT_k(B)|`. -/
def ProRelDistinguishes (S : Setoid (FP A B k)) : Prop :=
  ∃ x : FP A B k,
    ((mct A k).attach.filter fun p => S.r x (.inl p)).card ≠
      ((mct B k).attach.filter fun p => S.r x (.inr p)).card

/-- The flat tuple of a pro-tuple, as an element of `T_k(A) ∪ T_k(B)`. -/
noncomputable def fpFlat : FP A B k → FT A B k
  | .inl p => .inl ⟨p.1.2, snd_mem_flatTuples_of_mem_mct p.2⟩
  | .inr p => .inr ⟨p.1.2, snd_mem_flatTuples_of_mem_mct p.2⟩

/-- The profile of a pro-tuple. -/
def fpProfile : FP A B k → List σ.Sym
  | .inl p => p.1.1
  | .inr p => p.1.1

/-- `≡⁺` (p. 32): `(α, s) ≡⁺ (α′, s′)` iff `α = α′` and `s ≡ s′`. The map `𝔈 : ≡ ↦ ≡⁺`. -/
def plus (S : Setoid (FT A B k)) : Setoid (FP A B k) where
  r x y := fpProfile x = fpProfile y ∧ S.r (fpFlat x) (fpFlat y)
  iseqv := ⟨fun _ => ⟨rfl, S.refl _⟩, fun h => ⟨h.1.symm, S.symm h.2⟩,
    fun h h' => ⟨h.1.trans h'.1, S.trans h.2 h'.2⟩⟩

/-- The robust equivalence relations on `T_k(A) ∪ T_k(B)`. -/
def RobustRel (A : Structure σ V) (B : Structure σ W) (k : ℕ) : Type _ :=
  {S : Setoid (FT A B k) // Robust S}

/-- The pro-robust equivalence relations on `MCT_k(A) ∪ MCT_k(B)`. -/
def ProRobustRel (A : Structure σ V) (B : Structure σ W) (k : ℕ) : Type _ :=
  {S : Setoid (FP A B k) // ProRobust S}

/-- A map `𝔓` from robust to pro-robust equivalence relations is an **isomorphism**
(Definition 4.5, p. 31): (1) `𝔓` is a bijection; (2) `≡ ⊆ ≡′` iff `𝔓(≡) ⊆ 𝔓(≡′)`. -/
def IsIsoRP (P : RobustRel A B k → ProRobustRel A B k) : Prop :=
  Function.Bijective P ∧ ∀ S S' : RobustRel A B k, S.1 ≤ S'.1 ↔ (P S).1 ≤ (P S').1

end ProRobust

end HomIndGHW.RCR


