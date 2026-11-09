-- Prove2me | Definitions.Def_AutomaticSelfReduction_Lifting_Problem
-- name    : AutomaticSelfReduction_Lifting_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:01.339909+00:00
-- url     : https://prove2.me/theorems/374d1b13-6bac-4fcd-8e76-dae1de9e8d73
-- title:
--   Problems in the black-white formalism, configuration distance, 2-separation, b-dominance and round elimination
-- statement:
--   A **problem in the black-white formalism** is a tuple $\Pi=(\Sigma,\Delta,\delta,C_W,C_B)$: $\Sigma$ is a finite set of labels, $C_W$ is a set of multisets of size $\Delta$ over $\Sigma$ (white configurations) and $C_B$ is a set of multisets of size $\delta$ over $\Sigma$ (black configurations). Solving $\Pi$ on a $(\Delta,\delta)$-biregular 2-coloured graph means labelling every edge so that the multiset of labels around each white node lies in $C_W$ and around each black node lies in $C_B$. Throughout, $\Pi$ is **normalized**: $C_W$ and $C_B$ are nonempty, and the labels occurring in $C_W$, as well as those occurring in $C_B$, are exactly $\Sigma$.
--
--   For configurations $C_1,C_2$ of equal size, with $m_C(\ell)$ the multiplicity of $\ell$ in $C$,
--   $$
--   d(C_1,C_2)=\frac12\sum_{\ell}\lvert m_{C_1}(\ell)-m_{C_2}(\ell)\rvert,\qquad d(C_1,\mathcal C)=\min_{C_2\in\mathcal C}d(C_1,C_2)
--   $$
--   for a nonempty set $\mathcal C$; $d(C_1,C_2)$ is the least number of label substitutions turning $C_1$ into $C_2$.
--
--   1. $\Pi$ is **2-separated** if distinct configurations of $C_W$ have distance at least $2$, and distinct configurations of $C_B$ have distance at least $2$.
--   2. For an integer $b\ge 0$, $\Pi$ is **$b$-dominant** if every $C\in C_W$ has a label $\ell$ with $m_C(\ell)\ge\Delta-b$ and every $C\in C_B$ has a label $\ell$ with $m_C(\ell)\ge\delta-b$ (the label may depend on $C$).
--   3. **Round elimination** maps $\Pi$ to $R(\Pi)=(\Sigma',\delta,\Delta,C'_B,C'_W)$. Let $C'$ be the set of multisets $\{L_1,\dots,L_\delta\}$ of nonempty subsets of $\Sigma$ such that every choice $\ell_1\in L_1,\dots,\ell_\delta\in L_\delta$ gives $\{\ell_1,\dots,\ell_\delta\}\in C_B$; $C'_B$ consists of the maximal elements of $C'$ (no other $\{L'_1,\dots,L'_\delta\}\in C'$ admits a bijection $\varphi$ with $L_i\subseteq L'_{\varphi(i)}$ for all $i$); $\Sigma'$ is the set of sets occurring in $C'_B$; and $C'_W$ consists of the multisets $\{L_1,\dots,L_\Delta\}$ over $\Sigma'$ admitting a choice $\ell_i\in L_i$ with $\{\ell_1,\dots,\ell_\Delta\}\in C_W$.
--   4. Two problems are equal **up to renaming of labels** if a bijection between their label sets carries each constraint exactly onto the corresponding one.
--
--   These objects are the combinatorial layer of the lifting theorem: 2-separation and $b$-dominance define the class of problems it applies to, and $R$ is the operator whose iteration the lower bound follows.
--
--   **Formalization Note** The label set is a type `L` (finiteness is a hypothesis of each theorem). The degrees are type parameters, so `R P : Problem (RLabel P) δ Δ`, whose label type is the subtype $\Sigma'$ of `Finset L`; in the field order of the structure the first constraint `CW` of `R P` is $C'_B$ (the active side of degree $\delta$) and the second, `CB`, is $C'_W$. Choices are expressed with `Multiset.Rel`. The distance is computed in $\mathbb N$; for equal-size configurations the sum of absolute differences is even, so the halving is exact, and the distance to a nonempty set is a minimum of natural numbers. Normalization is a separate predicate because $R(\Pi)$ of an arbitrary problem need not be normalized.
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), Definitions 2.4–2.8 and the normalization assumption, printed pp. 6–8 (PDF pp. 7–9); round elimination R(Π), §4, printed p. 11 (PDF p. 12)

import Mathlib

/-!
# Problems in the black-white formalism and round elimination

Balliu, d'Amore, Olivetti, *Distributed Lower Bounds via Automatic Self-Reduction*,
STOC 2027 submission #338 (October 2026): Definitions 2.4–2.8 (PDF pp. 7–9, printed pp. 6–8)
and the round-elimination operator `R` of §4 (PDF p. 12, printed p. 11).

* `Problem L Δ δ`: label type `L` (the finite label set Σ, finiteness is a hypothesis
  `[Fintype L]` of the theorems), white constraint `CW` of size-`Δ` multisets, black
  constraint `CB` of size-`δ` multisets.
* `Problem.IsNormalized`: the standing assumption after Definition 2.4 (both constraints
  nonempty, and the labels occurring in `CW`, and those occurring in `CB`, are exactly `L`).
* `multisetDist`, `distToSet`: Definitions 2.5 and 2.6.
* `Problem.TwoSeparated`, `Problem.Dominant b`: Definitions 2.7 and 2.8.
* `R P : Problem (RLabel P) δ Δ`: round elimination; its labels are exactly the set `Σ'`.
* `Problem.Equiv`: equality of problems up to a renaming of labels.
-/

namespace AutomaticSelfReduction.Lifting

/-- Definition 2.4: a problem `(Σ, Δ, δ, C_W, C_B)` in the black-white formalism, with label
type `L`. Configurations are multisets; `CW` consists of multisets of size `Δ`, `CB` of
multisets of size `δ`. -/
structure Problem (L : Type*) (Δ δ : ℕ) where
  /-- The white constraint `C_W`. -/
  CW : Set (Multiset L)
  /-- The black constraint `C_B`. -/
  CB : Set (Multiset L)
  CW_card : ∀ C ∈ CW, Multiset.card C = Δ
  CB_card : ∀ C ∈ CB, Multiset.card C = δ

namespace Problem

variable {L : Type*} {Δ δ : ℕ}

/-- Standing assumption of the paper (PDF p. 7, after Definition 2.4): `C_W` and `C_B` are
nonempty, and the set of labels appearing in `C_W` and the set of labels appearing in `C_B`
are both exactly `Σ = L`. -/
def IsNormalized (P : Problem L Δ δ) : Prop :=
  P.CW.Nonempty ∧ P.CB.Nonempty ∧
    (∀ ℓ : L, ∃ C ∈ P.CW, ℓ ∈ C) ∧ (∀ ℓ : L, ∃ C ∈ P.CB, ℓ ∈ C)

/-- The same problem with the roles of the two sides exchanged:
`(Σ, Δ, δ, C_W, C_B) ↦ (Σ, δ, Δ, C_B, C_W)`. -/
def swap (P : Problem L Δ δ) : Problem L δ Δ where
  CW := P.CB
  CB := P.CW
  CW_card := P.CB_card
  CB_card := P.CW_card

end Problem

section Distance

variable {L : Type*} [DecidableEq L]

/-- Definition 2.5: `d(C₁, C₂) = (1/2) ∑_ℓ |m_{C₁}(ℓ) − m_{C₂}(ℓ)|`. The sum runs over the
labels occurring in `C₁` or `C₂` (all other terms vanish). For configurations of equal size the
sum of absolute differences is even, so the natural-number halving is exact. -/
def multisetDist (C₁ C₂ : Multiset L) : ℕ :=
  (∑ ℓ ∈ (C₁ + C₂).toFinset, Int.natAbs ((C₁.count ℓ : ℤ) - (C₂.count ℓ : ℤ))) / 2

/-- Definition 2.6: `d(C₁, 𝒞) = min_{C₂ ∈ 𝒞} d(C₁, C₂)` for a nonempty set `𝒞`. On a nonempty
set of natural numbers the infimum is attained, so it is the minimum. (Only applied to
nonempty constraints, by `Problem.IsNormalized`.) -/
noncomputable def distToSet (C₁ : Multiset L) (𝒞 : Set (Multiset L)) : ℕ :=
  sInf ((fun C₂ => multisetDist C₁ C₂) '' 𝒞)

end Distance

namespace Problem

variable {L : Type*} [DecidableEq L] {Δ δ : ℕ}

/-- Definition 2.7: distinct configurations of `C_W` have distance at least 2, and distinct
configurations of `C_B` have distance at least 2. -/
def TwoSeparated (P : Problem L Δ δ) : Prop :=
  (∀ C₁ ∈ P.CW, ∀ C₂ ∈ P.CW, C₁ ≠ C₂ → 2 ≤ multisetDist C₁ C₂) ∧
    (∀ C₁ ∈ P.CB, ∀ C₂ ∈ P.CB, C₁ ≠ C₂ → 2 ≤ multisetDist C₁ C₂)

end Problem

namespace Problem

variable {L : Type*} [DecidableEq L] {Δ δ : ℕ}

/-- Definition 2.8 (`b ≥ 0` an integer): every `C ∈ C_W` has a label `ℓ` with
`m_C(ℓ) ≥ Δ − b`, and every `C ∈ C_B` has a label `ℓ` with `m_C(ℓ) ≥ δ − b`. The dominant
label may depend on `C`. The inequality `m ≥ Δ − b` over the integers is written `Δ ≤ m + b`. -/
def Dominant (P : Problem L Δ δ) (b : ℕ) : Prop :=
  (∀ C ∈ P.CW, ∃ ℓ : L, Δ ≤ C.count ℓ + b) ∧ (∀ C ∈ P.CB, ∃ ℓ : L, δ ≤ C.count ℓ + b)

/-- Two problems are the same problem up to renaming of labels: a bijection of label types
carrying each constraint exactly onto the corresponding constraint. -/
structure Equiv {L₁ L₂ : Type*} (P₁ : Problem L₁ Δ δ) (P₂ : Problem L₂ Δ δ) where
  toEquiv : L₁ ≃ L₂
  CW_iff : ∀ C : Multiset L₁, C ∈ P₁.CW ↔ C.map toEquiv ∈ P₂.CW
  CB_iff : ∀ C : Multiset L₁, C ∈ P₁.CB ↔ C.map toEquiv ∈ P₂.CB

end Problem

/-! ### Round elimination (§4, PDF p. 12) -/

namespace Problem

variable {L : Type*} {Δ δ : ℕ}

/-- `{ℓ₁, …, ℓ_k}` is a choice from the multiset of sets `{L₁, …, L_k}`: one label from each
set, `ℓᵢ ∈ Lᵢ` after a suitable matching of positions. -/
def IsChoice (N : Multiset L) (M : Multiset (Finset L)) : Prop :=
  Multiset.Rel (fun ℓ S => ℓ ∈ S) N M

/-- The set `C'` of §4: multisets `{L₁, …, L_δ}` of nonempty subsets of `Σ` such that every
choice `ℓ₁ ∈ L₁, …, ℓ_δ ∈ L_δ` gives a configuration `{ℓ₁, …, ℓ_δ} ∈ C_B`. -/
def REAll (P : Problem L Δ δ) : Set (Multiset (Finset L)) :=
  {M | Multiset.card M = δ ∧ (∀ S ∈ M, S.Nonempty) ∧ ∀ N, IsChoice N M → N ∈ P.CB}

/-- `C'_B` of §4: the maximal configurations of `C'`, i.e. those `C = {L₁, …, L_δ}` for which no
other `C' = {L'₁, …, L'_δ} ∈ C'` with `C' ≠ C` admits a bijection `φ` with `Lᵢ ⊆ L'_{φ(i)}`. -/
def REMax (P : Problem L Δ δ) : Set (Multiset (Finset L)) :=
  {C | C ∈ P.REAll ∧ ∀ C' ∈ P.REAll, Multiset.Rel (fun S S' => S ⊆ S') C C' → C' = C}

/-- `Σ'` of §4: the sets appearing in at least one configuration of `C'_B`. -/
def RSigma (P : Problem L Δ δ) : Set (Finset L) :=
  {S | ∃ C ∈ P.REMax, S ∈ C}

end Problem

/-- The label type of `R(Π)`: exactly the elements of `Σ'`. -/
def RLabel {L : Type*} {Δ δ : ℕ} (P : Problem L Δ δ) : Type _ :=
  {S : Finset L // S ∈ P.RSigma}

instance {L : Type*} [DecidableEq L] {Δ δ : ℕ} (P : Problem L Δ δ) : DecidableEq (RLabel P) :=
  inferInstanceAs (DecidableEq {S : Finset L // S ∈ P.RSigma})

noncomputable instance {L : Type*} [Finite L] {Δ δ : ℕ} (P : Problem L Δ δ) :
    Fintype (RLabel P) :=
  @Fintype.ofFinite _ (inferInstanceAs (Finite {S : Finset L // S ∈ P.RSigma}))

/-- The round-elimination operator of §4: `R(Π) = (Σ', δ, Δ, C'_B, C'_W)`. In the tuple order
of Definition 2.4 the first ("white", active) constraint of `R(Π)` is `C'_B`, of size `δ`, and
the second ("black") constraint is `C'_W`: the multisets `{L₁, …, L_Δ}` of labels of `Σ'`
admitting a choice `ℓᵢ ∈ Lᵢ` with `{ℓ₁, …, ℓ_Δ} ∈ C_W`. -/
def R {L : Type*} {Δ δ : ℕ} (P : Problem L Δ δ) : Problem (RLabel P) δ Δ where
  CW := {M | M.map Subtype.val ∈ P.REMax}
  CB := {M | Multiset.card M = Δ ∧
    ∃ N : Multiset L, Problem.IsChoice N (M.map Subtype.val) ∧ N ∈ P.CW}
  CW_card := by
    intro M hM
    exact (Multiset.card_map Subtype.val M).symm.trans hM.1.1
  CB_card := fun _ hM => hM.1

end AutomaticSelfReduction.Lifting


