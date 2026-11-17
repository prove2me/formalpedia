-- Prove2me | Definitions.Def_FairFacilityLoc_Supplement_GeneralGroupStructure
-- name    : FairFacilityLoc_Supplement_GeneralGroupStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:27:33.908609+00:00
-- url     : https://prove2.me/theorems/67cfa770-d6ba-4513-95f8-04309e08ecbc
-- title:
--   Group-effect mechanism and ratio framework without sublinearity
-- statement:
--   Appendix E uses public group structures satisfying Definition 2.1 without assuming sublinearity. Such a structure consists of nonempty, possibly overlapping groups that cover all agents, together with a nonzero, monotone and symmetric effect for each group.
--
--   For these structures, the objective remains
--
--   $$
--   F(y;x,\mathcal G)=\max_j E_j\big((\lVert x_i-y\rVert_2)_{i\in G_j}\big),
--   \qquad \operatorname{OPT}(x,\mathcal G)=\inf_y F(y;x,\mathcal G).
--   $$
--
--   A deterministic mechanism maps every such public structure and profile to a facility location. Strategyproofness uses the same unilateral-deviation inequality as Definition 2.4. The per-instance, fixed-structure and superlinear-class ratios use the conventions $0/0=1$ and $a/0=\infty$ for $a>0$.
--
--   This framework isolates exactly the sublinearity assumption removed in Appendix E.
--
--   **Formalization Note** Facility locations are `EuclideanSpace ℝ (Fin d)`. Ratios and their suprema are in $[0,\infty]$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §2.1, pp.14–15 (PDF pp.16–17), and Appendix E, p.90 (PDF p.92)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_FairFacilityLoc_IsGroupEffect
import Definitions.Def_FairFacilityLoc_Supplement_IsSuperlinearEffect

open scoped NNReal ENNReal

namespace FairFacilityLoc.Supplement

set_option autoImplicit false

/-- A public group structure whose effects satisfy Definition 2.1 but are not required to be
sublinear (Yan–Zhou, *Fair and Strategyproof Facility Location in Euclidean Space*, manuscript,
sha256 642a1268…, Appendix E, p.90, PDF p.92).

**Formalization Note.** This is the published `FairFacilityLoc.GroupStructure` with only its
`isSublinear` field removed. Thus Appendix E can contain superlinear effects without falsely
asserting that they are sublinear. Agents and groups are 0-based `Fin n` and `Fin m`. -/
structure GeneralGroupStructure (n m : ℕ) where
  /-- The groups. -/
  G : Fin m → Finset (Fin n)
  /-- The group effects. -/
  E : ∀ j, (↥(G j) → ℝ≥0) → ℝ≥0
  /-- There is at least one group. -/
  m_pos : 0 < m
  /-- Every group is nonempty. -/
  nonempty : ∀ j, (G j).Nonempty
  /-- The groups cover every agent. -/
  cover : ∀ i, ∃ j, i ∈ G j

/-- The data in a general structure are admissible precisely when all effects satisfy Definition
2.1. Keeping this as a predicate, rather than a field, lets Theorem E.3 assert the printed
monotonicity and symmetry of `E_ε` rather than hiding them in a constructor proof. -/
def IsGeneralGroupStructure {n m : ℕ} (G : GeneralGroupStructure n m) : Prop :=
  ∀ j, FairFacilityLoc.IsGroupEffect (G.E j)

/-- The Appendix E distance vector. -/
noncomputable def generalDistanceVector {n m d : ℕ} (G : GeneralGroupStructure n m)
    (x : Fin n → GeoSemialgCSP.E d) (y : GeoSemialgCSP.E d) (j : Fin m) :
    ↥(G.G j) → ℝ≥0 :=
  fun i => ‖x i - y‖₊

/-- The Appendix E objective `F(y) = max_j E_j(u_j(y))`, using (2.1) without a sublinearity
assumption (Appendix E, p.90, PDF p.92). -/
noncomputable def generalObjective {n m d : ℕ} (G : GeneralGroupStructure n m)
    (x : Fin n → GeoSemialgCSP.E d) (y : GeoSemialgCSP.E d) : ℝ≥0 :=
  Finset.univ.sup fun j => G.E j (generalDistanceVector G x y j)

/-- The infimum of the Appendix E objective over all facility locations. -/
noncomputable def generalOptValue {n m d : ℕ} (G : GeneralGroupStructure n m)
    (x : Fin n → GeoSemialgCSP.E d) : ℝ≥0 :=
  ⨅ y : GeoSemialgCSP.E d, generalObjective G x y

/-- A deterministic mechanism defined on all group effects of Definition 2.1. -/
abbrev GeneralMechanism (d : ℕ) : Type :=
  ∀ {n m : ℕ}, GeneralGroupStructure n m →
    (Fin n → GeoSemialgCSP.E d) → GeoSemialgCSP.E d

/-- Strategyproofness in the unbundled Appendix E framework: the same incentive inequality as
Definition 2.4, now quantified over all Definition 2.1 group effects. -/
def GeneralIsStrategyproof {d : ℕ} (M : GeneralMechanism d) : Prop :=
  ∀ {n m : ℕ} (G : GeneralGroupStructure n m) (_hG : IsGeneralGroupStructure G)
    (x : Fin n → GeoSemialgCSP.E d) (i : Fin n) (x' : GeoSemialgCSP.E d),
      ‖x i - M G x‖ ≤ ‖x i - M G (Function.update x i x')‖

/-- The ratio at one Appendix E instance, with the paper's conventions `0/0 = 1` and
`a/0 = ∞` for `a > 0`. -/
noncomputable def generalRatioAt {n m d : ℕ} (M : GeneralMechanism d)
    (G : GeneralGroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) : ℝ≥0∞ :=
  if generalOptValue G x = 0 then
    (if generalObjective G x (M G x) = 0 then 1 else ⊤)
  else
    ((generalObjective G x (M G x) / generalOptValue G x : ℝ≥0) : ℝ≥0∞)

/-- The approximation ratio of a mechanism on one fixed public group structure. -/
noncomputable def ratioOn {n m d : ℕ} (M : GeneralMechanism d)
    (G : GeneralGroupStructure n m) : ℝ≥0∞ :=
  ⨆ x : Fin n → GeoSemialgCSP.E d, generalRatioAt M G x

/-- The approximation ratio restricted to superlinear group effects. It is the supremum over all
agent and group counts, all group structures whose effects are superlinear, and all profiles
(Appendix E.2, pp.90–92, PDF pp.92–94). -/
noncomputable def superlinearRatio {d : ℕ} (M : GeneralMechanism d) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (m : ℕ) (G : GeneralGroupStructure n m)
    (_hGroup : IsGeneralGroupStructure G)
    (_hG : ∀ j, IsSuperlinearEffect (G.E j))
    (x : Fin n → GeoSemialgCSP.E d), generalRatioAt M G x

end FairFacilityLoc.Supplement


