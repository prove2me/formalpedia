-- Prove2me | Definitions.Def_VAS5Reach_Supplement_IsTransArea
-- name    : VAS5Reach_Supplement_IsTransArea
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:48:13.139103+00:00
-- url     : https://prove2.me/theorems/ddeaa4f3-b754-4eec-b245-e99ce4269667
-- title:
--   Transformation areas and the sets $\mathcal T^i_C$, $\mathcal T_C$
-- statement:
--   Fix a $d$-VAS $V$ with transition set $T$. A set $A\subseteq\mathbb N^d$ is a **transformation area** if every $\mathbb Z$-run between configurations in $A$ can be rearranged into a run of $V$ with the same Parikh image: for all $s,t\in A$ and every word $\pi\in T^*$ with $s+\mathrm{EFF}(\pi)=t$ (intermediate values unconstrained) there is a run $s\xrightarrow{\rho}t$ in $V$ with $\psi_\rho=\psi_\pi$.
--
--   For $i\in[d]$ and $C\in\mathbb N$,
--   $$\mathcal T^i_C=\{x\in\mathbb N^d: x(j)\ge C\text{ for every }j\in[d]\setminus\{i\}\},\qquad \mathcal T_C=\bigcup_{i\in[d]}\mathcal T^i_C .$$
--
--   These are the objects of Theorem B.1, which quantifies van Leeuwen's transformation area.
--
--   **Formalization Note** The Parikh image is the published `VAS5Reach.parikh` (occurrence counts), so $\psi_\rho=\psi_\pi$ says $\rho$ is a permutation of $\pi$. Coordinates form a finite type $\iota$ with $d=|\iota|$.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), App. B, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_encode

namespace VAS5Reach.Supplement

open VAS5Reach

/-- A set `A ⊆ ℕ^d` of configurations of a `d`-VAS with transition set `T` is a
**transformation area** if every `ℤ`-run between configurations in `A` can be rearranged into a
run of the VAS with the same Parikh image: for all `s, t ∈ A` and every word `π` of transitions
of `T` with `s + EFF(π) = t` (intermediate values unconstrained), there is a run `s −ρ→ t`
(`IsVASRun`) with `ψ_ρ = ψ_π`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), App. B, printed p. 46
(PDF p. 48): "Fix a d-VAS V with transition set T. A set A ⊆ N^d is a transformation area if
every Z-run between configurations in A can be rearranged into a run in V with the same Parikh
image."

**Formalization Note** The Parikh image is the published `VAS5Reach.parikh` (occurrence counts),
so `ψ_ρ = ψ_π` says that `ρ` is a permutation of `π`. -/
def IsTransArea {ι : Type} (T : Finset (ι → ℤ)) (A : Set (ι → ℕ)) : Prop :=
  ∀ s ∈ A, ∀ t ∈ A, ∀ π : List (ι → ℤ), (∀ a ∈ π, a ∈ T) →
    (∀ i, (t i : ℤ) = (s i : ℤ) + π.sum i) →
    ∃ ρ, IsVASRun T s ρ t ∧ parikh ρ = parikh π

/-- `T^i_C := {x ∈ ℕ^d : x(j) ≥ C for every j ∈ [d] ∖ {i}}` (App. B, printed p. 46). -/
def TCi {ι : Type} (C : ℕ) (i : ι) : Set (ι → ℕ) :=
  {x | ∀ j, j ≠ i → C ≤ x j}

/-- `T_C := ⋃_{i ∈ [d]} T^i_C` (App. B, printed p. 46). -/
def TC {ι : Type} (C : ℕ) : Set (ι → ℕ) :=
  ⋃ i : ι, TCi C i

end VAS5Reach.Supplement


