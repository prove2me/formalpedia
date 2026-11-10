-- Prove2me | Definitions.Def_VAS5Reach_VASS_FwdCoverable
-- name    : VAS5Reach_VASS_FwdCoverable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:28:34.807747+00:00
-- url     : https://prove2.me/theorems/1932a18b-92e3-4197-9b64-601d0db15f20
-- title:
--   $C$-coverability, pumpability and $\mathrm{BD}(\pi, D)$
-- statement:
--   Let $(U, p(x), q(y))$ be a $d$-VASS with source and target configurations and let $C \in \mathbb N$ (Definition 6.7).
--   1. The source $p(x)$ is **forward $C$-coverable** in $U$ if $p(x) \xrightarrow{*} p(u)$ for some $u \ge C \cdot \mathbf 1$ (`FwdCoverable`).
--   2. The target $q(y)$ is **backward $C$-coverable** if $q(v) \xrightarrow{*} q(y)$ for some $v \ge C \cdot \mathbf 1$ (`BwdCoverable`).
--   3. The instance is **$C$-coverable** if both hold (`Coverable`), and **semi-$C$-coverable** if at least one holds (`SemiCoverable`).
--   4. $p(x)$ is **pumpable** if an enabled cycle returns to $p(x + a)$ for some $a \ge 0$, $a \ne 0$ (`Pumpable`).
--   5. For a run $\pi$ and $D \in \mathbb N$, $\mathrm{BD}(\pi, D)$ is the set of coordinates whose values remain below $D$ throughout $\pi$ (`BD`).
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Definition 6.7, p.27 (PDF p.29); semi-C-coverable p.31 (PDF p.33); pumpable p.32 (PDF p.34); BD p.16 (PDF p.18)

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun

namespace VAS5Reach

namespace VASS

variable {S ι : Type}

/-- Forward `C`-coverability (Definition 6.7): the source `p(x)` is forward `C`-coverable in `U`
if `p(x) −∗→ p(u)` in `U` for some `u ≥ C·1`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Definition 6.7, printed p. 27
(PDF p. 29): "Definition 6.7 (C-Coverability). Let (U, p(x), q(y)) be a d-VASS. For C ∈ N, the source
p(x) is forward C-coverable in U if p(x) −∗→ p(u) for some u ≥ C · 1. The target q(y) is backward
C-coverable if q(v) −∗→ q(y) for some v ≥ C · 1. The VASS (U, p(x), q(y)) is C-coverable if both
conditions hold." -/
def FwdCoverable (U : VASS S ι) (C : ℕ) (p : S) (x : ι → ℕ) : Prop :=
  ∃ u : ι → ℕ, (∀ i, C ≤ u i) ∧ Reach U p x p u

/-- Backward `C`-coverability (Definition 6.7): the target `q(y)` is backward `C`-coverable in
`U` if `q(v) −∗→ q(y)` in `U` for some `v ≥ C·1`. -/
def BwdCoverable (U : VASS S ι) (C : ℕ) (q : S) (y : ι → ℕ) : Prop :=
  ∃ v : ι → ℕ, (∀ i, C ≤ v i) ∧ Reach U q v q y

/-- `(U, p(x), q(y))` is `C`-coverable (Definition 6.7): the source is forward and the target
backward `C`-coverable. -/
def Coverable (U : VASS S ι) (C : ℕ) (p : S) (x : ι → ℕ) (q : S) (y : ι → ℕ) : Prop :=
  FwdCoverable U C p x ∧ BwdCoverable U C q y

/-- `(U, p(x), q(y))` is semi-`C`-coverable: its source is forward `C`-coverable or its target is
backward `C`-coverable (arXiv:2610.40012, §7, printed p. 31, PDF p. 33: "We call an instance
semi-C-coverable if its source is forward C-coverable or its target is backward C-coverable."). -/
def SemiCoverable (U : VASS S ι) (C : ℕ) (p : S) (x : ι → ℕ) (q : S) (y : ι → ℕ) : Prop :=
  FwdCoverable U C p x ∨ BwdCoverable U C q y

/-- `p(x)` is pumpable in `U`: an enabled cycle returns to `p(x + a)` for some `a ≥ 0`, `a ≠ 0`,
i.e. some nonempty path induces a run `p(x) −π→ p(y)` with `y ≥ x` and `y ≠ x`
(arXiv:2610.40012, §7.1, printed p. 32, PDF p. 34: "A configuration p(x) is pumpable in U if an
enabled cycle returns to p(x + a) for some a ≥ 0 with a ≠ 0."). -/
def Pumpable (U : VASS S ι) (p : S) (x : ι → ℕ) : Prop :=
  ∃ (π : List (S × (ι → ℤ) × S)) (y : ι → ℕ), π ≠ [] ∧ IsRun U p x π p y ∧ x ≤ y ∧ x ≠ y

/-- `BD(π, D)`: for a run `π` starting with counter vector `x`, the set of coordinates whose
values remain below `D` throughout `π` (at every intermediate configuration, including both
endpoints) (arXiv:2610.40012, §3, printed p. 16, PDF p. 18: "For a run π and a threshold D ∈ N,
let BD(π, D) denote the set of coordinates whose values remain below D throughout π.").

**Formalization Note** The starting counter vector `x` of the run is an explicit argument. -/
def BD (x : ι → ℕ) (π : List (S × (ι → ℤ) × S)) (D : ℕ) : Set ι :=
  {i | ∀ j ≤ π.length, (x i : ℤ) + eff (π.take j) i < D}

end VASS

end VAS5Reach


