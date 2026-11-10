-- Prove2me | Definitions.Def_StableCountSub3_RotationPoset
-- name    : StableCountSub3_RotationPoset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:47:53.368085+00:00
-- url     : https://prove2.me/theorems/ff81c57a-e70c-464a-b5ae-9e7b5d08884d
-- title:
--   Rotations of covers, the rotation poset, downsets, $D(\mu)$, $\mu_D$, boundaries and outward orders
-- statement:
--   The rotation structure of Section 2 for an instance $I$ with men and women indexed by $\{0,\dots,n-1\}$ (the published `StableMatching.Instance`; the order $\mu\preceq\mu'$ of Definition 2.3 is the published `StableCount.MatchingLE`, the cover relation $\mu\lessdot\mu'$ of Definition 2.5 is `StableCount.Covers`).
--
--   - `pairs μ` is $\mu$ as a set of (man, woman) pairs; `rotOf μ μ'` is the pair $(\mu\setminus\mu',\mu'\setminus\mu)$.
--   - **Rotation** (Definition 2.6): $\rho$ is a rotation if $\rho=(\mu\setminus\mu',\mu'\setminus\mu)$ for some stable $\mu\lessdot\mu'$; `rotations I` is the finite set $\mathcal R$.
--   - **Elimination** (Definition 2.7): `Eliminates I μ ρ μ'` means $\mu\lessdot\mu'$ and $\rho=(\mu\setminus\mu',\mu'\setminus\mu)$; $\rho$ is then exposed in $\mu$.
--   - **Rotation sequence** (Definition 2.8): `IsRotSeq I μ [ρ₁,…,ρ_k] μ'` says eliminating $\rho_1,\dots,\rho_k$ in order transforms the stable matching $\mu$ into $\mu'$.
--   - **Rotation poset** (Definition 2.9): $\rho\prec\rho'$ iff in every rotation sequence in which both are eliminated, $\rho$ comes before $\rho'$ (first occurrences); $\rho\preceq\rho'$ iff $\rho=\rho'$ or $\rho\prec\rho'$. A **downset** is $D\subseteq\mathcal R$ with $\rho\in D$, $\rho'\in\mathcal R$, $\rho'\preceq\rho$ implying $\rho'\in D$; `downsets I` is the set of all of them.
--   - A **linear extension** of $D$ (footnote 3) is a duplicate-free list of the elements of $D$ in which $x\preceq y$ implies that $x$ comes no later than $y$.
--   - `mopt I` is the man-optimal stable matching $\mu_{m\text{-opt}}$ (`StableCount.IsManOptimal`; it exists and is unique by Theorem 2.4). `Dof I μ` is $D(\mu)$, the set of rotations of a rotation sequence from $\mu_{m\text{-opt}}$ to $\mu$; `muOf I D` is $\mu_D$, the result of eliminating $D$ from $\mu_{m\text{-opt}}$ along a linear extension. Both are chosen among the objects the page describes; their uniqueness is Theorem 2.10, and the fallback values ($\emptyset$, $\mu_{m\text{-opt}}$) are never reached for stable matchings and downsets.
--   - $M(\rho)=\{m:(m,w)\in\mu\setminus\mu'\text{ for some }w\}$ (`participants`), $C_m=\{\rho\in\mathcal R: m\in M(\rho)\}$ (`mchain`), and the **boundary** $T_m(D)=|D\cap C_m|$ (Definition 2.12).
--   - **Outward orders** (Definition 2.14): the forward order $P^+(D)$ is $\preceq$ on $\mathcal R\setminus D$, the backward order $P^-(D)$ is the reverse of $\preceq$ on $D$ (`carrier`, `outLE`, strict `outLT`); `IsMinOut` is membership in $\min P^\pm(D)$.
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Definitions 2.1–2.9, 2.12, 2.14 and §2.3, pp. 7–10 (PDF 9–12)

import Mathlib
import Definitions.Def_StableMatching_GaleShapley
import Definitions.Def_StableCount_Count
import Definitions.Def_StableCount_Rotation

open StableMatching

noncomputable section

namespace StableCountSub3

variable {n : ℕ}

/-- The matched pairs of a perfect matching `μ`, as a set of (man, woman) pairs
(Definition 2.1: a perfect matching is a subset of `M × W`, identified with a bijection). -/
def pairs (μ : Matching n) : Finset (Fin n × Fin n) :=
  Finset.univ.image fun m => (m, μ m)

/-- A candidate rotation: a pair of sets of (man, woman) pairs. -/
abbrev Rot (n : ℕ) := Finset (Fin n × Fin n) × Finset (Fin n × Fin n)

/-- The pair `(μ \ μ', μ' \ μ)` of two matchings (Definition 2.6). -/
def rotOf (μ μ' : Matching n) : Rot n :=
  (pairs μ \ pairs μ', pairs μ' \ pairs μ)

/-- Definition 2.6: `ρ` is a rotation if `ρ = (μ \ μ', μ' \ μ)` for some stable matchings with
`μ ⋖ μ'` (the cover relation of Definition 2.5 in the order of Definition 2.3, i.e. the published
`StableCount.Covers`). -/
def IsRotation (I : Instance n) (ρ : Rot n) : Prop :=
  ∃ μ μ' : Matching n, StableCount.Covers I μ μ' ∧ rotOf μ μ' = ρ

/-- `ℛ`, the (finite) set of all rotations of `I`. -/
def rotations (I : Instance n) : Finset (Rot n) := by
  classical
  exact Finset.univ.filter (IsRotation I)

/-- Definition 2.7: eliminating the rotation `ρ` exposed in `μ` transforms `μ` into `μ'`:
`μ ⋖ μ'` and `ρ = (μ \ μ', μ' \ μ)`. -/
def Eliminates (I : Instance n) (μ : Matching n) (ρ : Rot n) (μ' : Matching n) : Prop :=
  StableCount.Covers I μ μ' ∧ rotOf μ μ' = ρ

/-- Definition 2.7: `ρ` is exposed in `μ`. -/
def IsExposed (I : Instance n) (ρ : Rot n) (μ : Matching n) : Prop :=
  ∃ μ', Eliminates I μ ρ μ'

/-- Definition 2.8: `IsRotSeq I μ [ρ₁, …, ρ_k] μ'` says that eliminating `ρ₁, …, ρ_k` in this
order transforms the stable matching `μ` into `μ'` (a rotation sequence from `μ` to `μ'`).
The empty sequence goes from a stable matching to itself. -/
inductive IsRotSeq (I : Instance n) : Matching n → List (Rot n) → Matching n → Prop
  | nil (μ : Matching n) : I.IsStable μ → IsRotSeq I μ [] μ
  | cons {μ ν μ' : Matching n} {ρ : Rot n} {l : List (Rot n)} :
      Eliminates I μ ρ ν → IsRotSeq I ν l μ' → IsRotSeq I μ (ρ :: l) μ'

/-- Definition 2.9: `ρ ≺ ρ'` when `ρ` precedes `ρ'` in every rotation sequence in which both are
eliminated (position of the first occurrence). -/
def RotPrec (I : Instance n) (ρ ρ' : Rot n) : Prop :=
  ∀ (μ : Matching n) (l : List (Rot n)) (μ' : Matching n),
    IsRotSeq I μ l μ' → ρ ∈ l → ρ' ∈ l → l.idxOf ρ < l.idxOf ρ'

/-- Definition 2.9: `ρ ⪯ ρ'` iff `ρ = ρ'` or `ρ ≺ ρ'` (the rotation poset `(ℛ, ⪯)`). -/
def RotLE (I : Instance n) (ρ ρ' : Rot n) : Prop :=
  ρ = ρ' ∨ RotPrec I ρ ρ'

/-- Definition 2.9: `D ⊆ ℛ` is a downset of `(ℛ, ⪯)`. -/
def IsDownset (I : Instance n) (D : Finset (Rot n)) : Prop :=
  D ⊆ rotations I ∧ ∀ ρ ∈ D, ∀ ρ' ∈ rotations I, RotLE I ρ' ρ → ρ' ∈ D

/-- The finite set of all downsets of `(ℛ, ⪯)`. -/
def downsets (I : Instance n) : Finset (Finset (Rot n)) := by
  classical
  exact (rotations I).powerset.filter (IsDownset I)

/-- Footnote 3: a linear extension of the downset `D` (as a subposet of `(ℛ, ⪯)`), written as a
duplicate-free list of the elements of `D` in which `x ⪯ y` implies that `x` comes no later
than `y`. -/
def IsLinExt (I : Instance n) (D : Finset (Rot n)) (l : List (Rot n)) : Prop :=
  l.Nodup ∧ l.toFinset = D ∧ ∀ i j : Fin l.length, RotLE I (l.get i) (l.get j) → i ≤ j

open Classical in
/-- `μ_{m-opt}` (Definition 2.3): the man-optimal stable matching, i.e. the matching satisfying the
published `StableCount.IsManOptimal` (stable, and every man weakly prefers it to every stable
matching). It exists and is unique (Theorem 2.4); the value `Equiv.refl` is used only if no
such matching existed, which never happens. -/
def mopt (I : Instance n) : Matching n :=
  if h : ∃ μ, StableCount.IsManOptimal I μ then h.choose else Equiv.refl _

open Classical in
/-- `D(μ)` (§2.3): the set of rotations eliminated in a rotation sequence from `μ_{m-opt}` to
`μ` (unique by Theorem 2.10 (i)); `∅` if no such sequence exists. -/
def Dof (I : Instance n) (μ : Matching n) : Finset (Rot n) :=
  if h : ∃ l, IsRotSeq I (mopt I) l μ then h.choose.toFinset else ∅

open Classical in
/-- `μ_D` (Theorem 2.10 (ii)): the matching obtained from `μ_{m-opt}` by eliminating the rotations
of `D` along a linear extension of `D`; `μ_{m-opt}` if no linear extension of `D` is a rotation
sequence from `μ_{m-opt}`. -/
def muOf (I : Instance n) (D : Finset (Rot n)) : Matching n :=
  if h : ∃ l μ, IsLinExt I D l ∧ IsRotSeq I (mopt I) l μ then h.choose_spec.choose else mopt I

/-- `M(ρ)` (§2.3): the men participating in `ρ = (μ \ μ', μ' \ μ)`, i.e. the men `m` with
`(m, w) ∈ μ \ μ'` for some `w`. -/
def participants (ρ : Rot n) : Finset (Fin n) :=
  ρ.1.image Prod.fst

/-- `C_m = {ρ ∈ ℛ : m ∈ M(ρ)}` (§2.3), the rotations involving the man `m` (the `m`-chain). -/
def mchain (I : Instance n) (m : Fin n) : Finset (Rot n) := by
  classical
  exact (rotations I).filter fun ρ => m ∈ participants ρ

/-- Definition 2.12: the boundary `T_m(D) = |D ∩ C_m|` of `D` at the man `m`. -/
def boundary (I : Instance n) (m : Fin n) (D : Finset (Rot n)) : ℕ := by
  classical
  exact (D ∩ mchain I m).card

/-- The two outward directions (Definition 2.14): forward (`+`) and backward (`−`). -/
inductive Dir where
  | fwd
  | bwd
  deriving DecidableEq

/-- The ground set of the outward order from `D` (Definition 2.14): `ℛ \ D` for the forward
order `P⁺(D)`, `D` for the backward order `P⁻(D)`. -/
def carrier (I : Instance n) (D : Finset (Rot n)) : Dir → Finset (Rot n)
  | .fwd => rotations I \ D
  | .bwd => D

/-- The order of the outward orders (Definition 2.14): `⪯` itself for `P⁺(D)`, the reverse of `⪯`
for `P⁻(D)`. `outLE I dir ρ ρ'` reads "`ρ` comes weakly before `ρ'` in direction `dir`". -/
def outLE (I : Instance n) : Dir → Rot n → Rot n → Prop
  | .fwd, ρ, ρ' => RotLE I ρ ρ'
  | .bwd, ρ, ρ' => RotLE I ρ' ρ

/-- Strict precedence in the outward order: `ρ` comes before `ρ' ≠ ρ`. -/
def outLT (I : Instance n) (dir : Dir) (ρ ρ' : Rot n) : Prop :=
  outLE I dir ρ ρ' ∧ ρ ≠ ρ'

/-- `ρ ∈ min P^dir(D)` (before Lemma 2.16): `ρ` is a minimal element of the outward order. -/
def IsMinOut (I : Instance n) (D : Finset (Rot n)) (dir : Dir) (ρ : Rot n) : Prop :=
  ρ ∈ carrier I D dir ∧ ∀ ρ' ∈ carrier I D dir, outLE I dir ρ' ρ → ρ' = ρ

end StableCountSub3


