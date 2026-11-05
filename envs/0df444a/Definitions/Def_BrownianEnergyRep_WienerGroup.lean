-- Prove2me | Definitions.Def_BrownianEnergyRep_WienerGroup
-- name    : BrownianEnergyRep_WienerGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:32.728911+00:00
-- url     : https://prove2.me/theorems/84221fc2-8def-4f33-a0ff-dbde42f49b0c
-- title:
--   Wiener space $W(G)$ of continuous paths in $G$ from $e$
-- statement:
--   For $0<T<\infty$, Wiener space is
--   $$
--   W(G)=\{\gamma\in C([0,T],G):\gamma_0=e\},
--   $$
--   a group under pointwise multiplication $(hk)_t=h_tk_t$, with inversion $\Theta(\gamma)=\gamma^{-1}$ and projections $g_t(\gamma)=\gamma_t$. It carries the Borel $\sigma$-algebra of the uniform metric.
--
--   **Formalization Note** $W(G)$ is a subgroup of $C([0,T],\mathrm{GL}_n(\mathbb R))$ with the compact-open topology, which on the compact group $G$ is the topology of the uniform metric $d_\infty$. So the Borel sets are the same. The module also defines the evaluations $\gamma_t$ for real $t$, by the nearest endpoint outside $[0,T]$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Notation 2.3(1), p.3

import Mathlib
import Definitions.Def_BrownianEnergyRep_IsSmoothOnGroup

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Wiener space `W(G) = {γ ∈ C([0,T], G) : γ₀ = e}` with pointwise multiplication
(arXiv:1511.07378v1, Notation 2.3(1), p.3).

**Formalization Note** `W(G)` is a subgroup of `C([0,T], GLₙ(ℝ))` with the compact-open topology
and its Borel σ-algebra. As `G` is compact, this topology is that of the uniform metric `d_∞`, so
the Borel sets agree with the page's. -/
def WienerGroup {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) (T : ℝ) [hT : Fact (0 < T)] :
    Subgroup C(Icc (0 : ℝ) T, GL (Fin n) ℝ) where
  carrier := {γ | (∀ t, γ t ∈ G) ∧ γ ⟨0, le_rfl, hT.out.le⟩ = 1}
  mul_mem' := fun ha hb =>
    ⟨fun t => G.mul_mem (ha.1 t) (hb.1 t), by simp [ha.2, hb.2]⟩
  one_mem' := ⟨fun _ => G.one_mem, rfl⟩
  inv_mem' := fun ha => ⟨fun t => G.inv_mem (ha.1 t), by simp [ha.2]⟩

instance wienerGroupMeasurableSpace {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) (T : ℝ)
    [Fact (0 < T)] : MeasurableSpace ↥(WienerGroup G T) := borel _

instance wienerGroupBorelSpace {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) (T : ℝ)
    [Fact (0 < T)] : BorelSpace ↥(WienerGroup G T) := ⟨rfl⟩

/-- The projection `g_t(γ) = γ_t ∈ G` (arXiv:1511.07378v1, Notation 2.3(1), p.3).

**Formalization Note** For `t` outside `[0,T]` this is the value at the nearest endpoint. -/
noncomputable def pathAt {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {T : ℝ} [hT : Fact (0 < T)]
    (γ : ↥(WienerGroup G T)) (t : ℝ) : ↥G :=
  ⟨γ.1 (projIcc 0 T hT.out.le t), γ.2.1 _⟩

/-- `γ_t` as a matrix. -/
noncomputable def matAt {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {T : ℝ} [Fact (0 < T)]
    (γ : ↥(WienerGroup G T)) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (((pathAt γ t : ↥G) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)

end BrownianEnergyRep


