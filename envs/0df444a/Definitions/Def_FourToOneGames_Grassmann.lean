-- Prove2me | Definitions.Def_FourToOneGames_Grassmann
-- name    : FourToOneGames_Grassmann
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T23:02:46.915535+00:00
-- url     : https://prove2.me/theorems/b9d39d00-9551-489d-97c4-af49af199ebc
-- title:
--   The Grassmann graph over $\mathbb{F}_2$ and its agreement tests
-- statement:
--   The objects needed to state the Grassmann decoding theorems (Theorems 3.2 and 3.3 of the source paper).
--
--   The ambient space is $\mathbb{F}_2^n$, and $\mathrm{Gr}(\mathbb{F}_2^n,\ell)$ is the set of its $\ell$-dimensional subspaces. The **Grassmann graph** has vertex set $\mathrm{Gr}(\mathbb{F}_2^n,\ell)$, with an edge between $L_1$ and $L_2$ when $\dim(L_1 \cap L_2) = \ell - 1$; probabilities over a random edge or a random subspace are ratios of cardinalities of these finite sets, a ratio with empty denominator being $0$.
--
--   A **table** $F$ assigns to each subspace $L$ either a linear functional on $L$, or the nullity element $\mathrm{nil}$; a set-valued table assigns an element of a finite set $\Sigma$ or $\mathrm{nil}$. The **Grassmann test** accepts a random edge $(L_1,L_2)$ when both entries are non-nil and agree on $L_1 \cap L_2$; the **equality test** accepts when both entries are non-nil and equal. For a zoom-in $Q$ and a zoom-out $W$, the agreement of $F$ with a linear functional $f : W \to \mathbb{F}_2$ (respectively with a constant $\sigma$) is the fraction of $\ell$-dimensional $L$ with $Q \subseteq L \subseteq W$ on which $F[L] = f|_L$ (respectively $F[L] = \sigma$).
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, pp. 15-16, Section 3.2.2 (Theorems 3.2 and 3.3) and Definition 3.7

import Mathlib

/-!
# The Grassmann graph, Grassmann tables, and their agreement tests

Objects needed to state the Grassmann decoding theorems (Theorems 3.2 and 3.3) of
Fei–Minzer–Wang, *On the Hardness of 4-to-1 Games with Perfect Completeness* (ECCC TR26-179).

Throughout, the ambient space is `F₂ⁿ`, modelled as `Fin n → ZMod 2`.  All probabilities are
uniform distributions over finite sets of subspaces and are written as ratios of cardinalities
(`Set.ncard`); a ratio with an empty denominator evaluates to `0`.
-/

namespace FourToOneGames

/-- The ambient space `F₂ⁿ`. -/
abbrev Fspace (n : ℕ) : Type := Fin n → ZMod 2

/-- `Gr(F₂ⁿ, ℓ)`, the set of `ℓ`-dimensional linear subspaces of `F₂ⁿ`. -/
def Gr (n ℓ : ℕ) : Set (Submodule (ZMod 2) (Fspace n)) :=
  {W | Module.finrank (ZMod 2) W = ℓ}

/-- The codimension of a subspace of `F₂ⁿ`. -/
noncomputable def codim {n : ℕ} (W : Submodule (ZMod 2) (Fspace n)) : ℕ :=
  n - Module.finrank (ZMod 2) W

/-- The codimension of `W'` inside `W`, for `W' ≤ W`. -/
noncomputable def relCodim {n : ℕ} (W W' : Submodule (ZMod 2) (Fspace n)) : ℕ :=
  Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) W'

/-- The edge set of the Grassmann graph on `Gr(F₂ⁿ, ℓ)`: ordered pairs of `ℓ`-dimensional
subspaces meeting in dimension `ℓ - 1`. -/
def GrEdges (n ℓ : ℕ) : Set (Submodule (ZMod 2) (Fspace n) × Submodule (ZMod 2) (Fspace n)) :=
  {p | p.1 ∈ Gr n ℓ ∧ p.2 ∈ Gr n ℓ ∧ Module.finrank (ZMod 2) ↥(p.1 ⊓ p.2) = ℓ - 1}

/-- The probability that a uniformly random edge `(L₁, L₂)` of the Grassmann graph satisfies the
predicate `P`. -/
noncomputable def grEdgeProb (n ℓ : ℕ)
    (P : Submodule (ZMod 2) (Fspace n) → Submodule (ZMod 2) (Fspace n) → Prop) : ℝ :=
  ({p ∈ GrEdges n ℓ | P p.1 p.2}.ncard : ℝ) / ((GrEdges n ℓ).ncard : ℝ)

/-- The fraction of `q`-dimensional subspaces `Q` of `F₂ⁿ` satisfying the predicate `P`. -/
noncomputable def grFraction (n q : ℕ) (P : Submodule (ZMod 2) (Fspace n) → Prop) : ℝ :=
  ({Q ∈ Gr n q | P Q}.ncard : ℝ) / ((Gr n q).ncard : ℝ)

/-- A table assigning to every subspace `L` of `F₂ⁿ` either a linear functional on `L`, or the
nullity element (`none`). -/
abbrev LinTable (n : ℕ) : Type :=
  (L : Submodule (ZMod 2) (Fspace n)) → Option (L →ₗ[ZMod 2] ZMod 2)

/-- The restriction of a linear functional on `W` to a subspace `L ≤ W`. -/
def restrictLE {n : ℕ} {L W : Submodule (ZMod 2) (Fspace n)} (h : L ≤ W)
    (f : W →ₗ[ZMod 2] ZMod 2) : L →ₗ[ZMod 2] ZMod 2 :=
  f ∘ₗ Submodule.inclusion h

/-- The Grassmann test event: the entries of the table `F` at `L₁` and `L₂` are both non-nil and
agree on `L₁ ∩ L₂`. -/
def AgreeOnInter {n : ℕ} (F : LinTable n)
    (L₁ L₂ : Submodule (ZMod 2) (Fspace n)) : Prop :=
  ∃ f₁ f₂, F L₁ = some f₁ ∧ F L₂ = some f₂ ∧
    restrictLE (inf_le_left : L₁ ⊓ L₂ ≤ L₁) f₁ = restrictLE (inf_le_right : L₁ ⊓ L₂ ≤ L₂) f₂

/-- The probability that the Grassmann test accepts the table `F`, i.e. that a uniformly random
edge `(L₁, L₂)` of the Grassmann graph has `F[L₁]` and `F[L₂]` agreeing on `L₁ ∩ L₂`. -/
noncomputable def grTestProb {n : ℕ} (ℓ : ℕ) (F : LinTable n) : ℝ :=
  grEdgeProb n ℓ (AgreeOnInter F)

/-- The fraction of `ℓ`-dimensional subspaces `L` with `Q ⊆ L ⊆ W` on which the table `F` agrees
with the restriction of the linear functional `f : W → F₂`. -/
noncomputable def zoomAgreementLin {n : ℕ} (ℓ : ℕ) (F : LinTable n)
    (Q W : Submodule (ZMod 2) (Fspace n)) (f : W →ₗ[ZMod 2] ZMod 2) : ℝ :=
  ({L ∈ Gr n ℓ | Q ≤ L ∧ ∃ h : L ≤ W, F L = some (restrictLE h f)}.ncard : ℝ) /
    ({L ∈ Gr n ℓ | Q ≤ L ∧ L ≤ W}.ncard : ℝ)

/-- A table assigning to every subspace `L` of `F₂ⁿ` either an element of `σType`, or the nullity
element (`none`). -/
abbrev SetTable (n : ℕ) (σType : Type) : Type :=
  Submodule (ZMod 2) (Fspace n) → Option σType

/-- The probability that the *equality test* accepts the table `F`, i.e. that a uniformly random
edge `(L₁, L₂)` of the Grassmann graph has `F[L₁] = F[L₂] ≠ nil`. -/
noncomputable def grEqualityTestProb {n : ℕ} {σType : Type} (ℓ : ℕ) (F : SetTable n σType) : ℝ :=
  grEdgeProb n ℓ fun L₁ L₂ => ∃ σ : σType, F L₁ = some σ ∧ F L₂ = some σ

/-- The fraction of `ℓ`-dimensional subspaces `L` with `Q ⊆ L ⊆ W` on which the table `F` takes
the value `σ`. -/
noncomputable def zoomAgreementConst {n : ℕ} {σType : Type} (ℓ : ℕ) (F : SetTable n σType)
    (Q W : Submodule (ZMod 2) (Fspace n)) (σ : σType) : ℝ :=
  ({L ∈ Gr n ℓ | Q ≤ L ∧ L ≤ W ∧ F L = some σ}.ncard : ℝ) /
    ({L ∈ Gr n ℓ | Q ≤ L ∧ L ≤ W}.ncard : ℝ)

end FourToOneGames


