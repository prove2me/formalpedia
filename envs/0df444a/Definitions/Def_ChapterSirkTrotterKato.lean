-- Prove2me | Definitions.Def_ChapterSirkTrotterKato
-- name    : ChapterSirkTrotterKato
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T05:15:47.292315+00:00
-- url     : https://prove2.me/theorems/d9fb4c74-70d4-4942-b086-0479272c3888
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 3** asks for the transfer of generator convergence to the *unitary group*: `e^{−itAₙ} ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkTrotterKato`, source chapter `BookProof/ChapterSirkTrotterKato.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 3** asks for the transfer of generator convergence to the *unitary group*: `e^{−itAₙ} → e^{−itA}` strongly, locally uniformly in `t`. `ChapterSirkGroupTransfer` settled the **bounded** half (norm convergence of bounded generators, with an explicit rate). This chapter settles the **unbounded** half — the Trotter–Kato theorem itself — for the unbounded self-adjoint operators of `ChapterStoneResolvent`, i.e. exactly the objects the selection theorems of the project produce:
--
--   > if the resolvents `(Aₙ − i)⁻¹` converge strongly to `(A − i)⁻¹`, then > `e^{−itAₙ} v → e^{−itA} v` for every `v`, uniformly for `t` in a bounded > interval.
--
--   The proof is the classical Duhamel argument, formalized in four steps.
--
--   * `hasDerivAt_stoneU_const_sub` — the backwards flow `r ↦ e^{−i(t−r)A} z` differentiates to `+ i A` on the domain. * `hasDerivAt_stoneU_const_sub_apply` — the **weak product rule**: the flow is only strongly continuous, so `r ↦ e^{−i(t−r)A} (y r)` cannot be differentiated by the ordinary product rule; it is differentiated here from the definition, for a curve `y` differentiable at the point and taking its value there in the domain. * `resolvent_commutator_eq` — the algebraic heart, `Aₛ Rₛ − Rₛ A = (R − Rₛ)(A − i)` on `dom A`, where `R = (A − i)⁻¹` and `Rₛ = (Aₛ − i)⁻¹`. * `hasDerivAt_duhamel` — the Duhamel derivative `d/dr [ e^{−i(t−r)Aₛ} Rₛ e^{−irA} χ ] = i e^{−i(t−r)Aₛ} (R − Rₛ) e^{−irA}(A − i)χ`, and `norm_res_stoneU_sub_stoneU_res_le` — the resulting mean-value estimate.
--
--   The convergence statements are `trotterKato_uniform_of_mem_range` (on the dense set `R(dom A)`), `trotterKato_uniform_on_interval` and `trotterKato_tendstoUniformlyOn` (**the headline: locally uniformly in `t`**) and `trotterKato_tendsto` (strong convergence at a fixed time). The auxiliary `tendsto_uniformly_on_isCompact_of_tendsto` is the standard equi-Lipschitz upgrade of pointwise convergence to uniform convergence on a compact set.
--
--   Strong resolvent convergence is *assumed* at the single point `i` of the resolvent set, which is all the theorem needs; nothing here proves that the Galerkin/Hashimoto compressions of a given physical Hamiltonian satisfy it — that is the content of the per-system selection theorems, which the project proves separately. Together with those, this chapter closes the transfer step: the flow of the selected generator is the limit of the approximating flows.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkTrotterKato.lean

import Definitions.Def_ChapterStoneGenerator
import Mathlib

import Mathlib

/-!
# Chapter SirkTrotterKato — the unbounded half of §12 Gap 3 (Trotter–Kato)

`CONSOLIDATED_PLAN.md` §12.2 **Gap 3** asks for the transfer of generator
convergence to the *unitary group*: `e^{−itAₙ} → e^{−itA}` strongly, locally
uniformly in `t`.  `ChapterSirkGroupTransfer` settled the **bounded** half (norm
convergence of bounded generators, with an explicit rate).  This chapter settles
the **unbounded** half — the Trotter–Kato theorem itself — for the unbounded
self-adjoint operators of `ChapterStoneResolvent`, i.e. exactly the objects the
selection theorems of the project produce:

> if the resolvents `(Aₙ − i)⁻¹` converge strongly to `(A − i)⁻¹`, then
> `e^{−itAₙ} v → e^{−itA} v` for every `v`, uniformly for `t` in a bounded
> interval.

The proof is the classical Duhamel argument, formalized in four steps.

* `hasDerivAt_stoneU_const_sub` — the backwards flow `r ↦ e^{−i(t−r)A} z`
  differentiates to `+ i A` on the domain.
* `hasDerivAt_stoneU_const_sub_apply` — the **weak product rule**: the flow is
  only strongly continuous, so `r ↦ e^{−i(t−r)A} (y r)` cannot be differentiated
  by the ordinary product rule; it is differentiated here from the definition,
  for a curve `y` differentiable at the point and taking its value there in the
  domain.
* `resolvent_commutator_eq` — the algebraic heart, `Aₛ Rₛ − Rₛ A = (R − Rₛ)(A − i)`
  on `dom A`, where `R = (A − i)⁻¹` and `Rₛ = (Aₛ − i)⁻¹`.
* `hasDerivAt_duhamel` — the Duhamel derivative
  `d/dr [ e^{−i(t−r)Aₛ} Rₛ e^{−irA} χ ] = i e^{−i(t−r)Aₛ} (R − Rₛ) e^{−irA}(A − i)χ`,
  and `norm_res_stoneU_sub_stoneU_res_le` — the resulting mean-value estimate.

The convergence statements are `trotterKato_uniform_of_mem_range` (on the dense
set `R(dom A)`), `trotterKato_uniform_on_interval` and
`trotterKato_tendstoUniformlyOn` (**the headline: locally uniformly in `t`**) and
`trotterKato_tendsto` (strong convergence at a fixed time).  The auxiliary
`tendsto_uniformly_on_isCompact_of_tendsto` is the standard equi-Lipschitz upgrade
of pointwise convergence to uniform convergence on a compact set.

## Honest boundary

Strong resolvent convergence is *assumed* at the single point `i` of the
resolvent set, which is all the theorem needs; nothing here proves that the
Galerkin/Hashimoto compressions of a given physical Hamiltonian satisfy it — that
is the content of the per-system selection theorems, which the project proves
separately.  Together with those, this chapter closes the transfer step: the
flow of the selected generator is the limit of the approximating flows.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace

namespace BookProof.ChapterSirkTrotterKato

open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## 1. Differentiating the backwards flow -/







/-! ## 2. The Duhamel derivative -/









/-! ## 3. Pointwise convergence upgraded on compact sets -/



/-! ## 4. Trotter–Kato -/

variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

/-- Strong convergence of the resolvents at the point `i` of the resolvent set. -/
def StrongResolventConvergence : Prop :=
  ∀ y : H, Tendsto (fun n => (S n).resCLM 1 y) atTop (𝓝 (T.resCLM 1 y))

/-- The resolvent difference, as a bounded operator. -/
def resDiff (n : ℕ) : H →L[ℂ] H := T.resCLM 1 - (S n).resCLM 1

















end BookProof.ChapterSirkTrotterKato

namespace BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace UnboundedSelfAdjoint

variable (T : UnboundedSelfAdjoint H)

theorem yosidaGen_commute_resCLM (n l : ℝ) : Commute (T.yosidaGen n) (T.resCLM l) := by
  have h : ∀ a b : ℝ, Commute (T.resCLM a) (T.resCLM b) := T.resCLM_commute
  have hy : Commute (T.yosida n) (T.resCLM l) := by
    unfold yosida
    refine Commute.add_left (Commute.smul_left ?_ _) (Commute.smul_left ?_ _)
    · exact h _ _
    · exact (h _ _).mul_left (h _ _)
  exact hy.smul_left _

theorem approxU_commute_resCLM (n t l : ℝ) : Commute (T.approxU n t) (T.resCLM l) :=
  (((T.yosidaGen_commute_resCLM n l).smul_left t)).exp_left

theorem stoneU_commute_resCLM (t l : ℝ) (y : H) :
    T.stoneU t (T.resCLM l y) = T.resCLM l (T.stoneU t y) := by
  have h1 : Tendsto (fun k : ℕ => T.approxU ((k : ℝ) + 1) t (T.resCLM l y)) atTop
      (𝓝 (T.stoneU t (T.resCLM l y))) := T.tendsto_stoneU t _
  have h2 : Tendsto (fun k : ℕ => T.resCLM l (T.approxU ((k : ℝ) + 1) t y)) atTop
      (𝓝 (T.resCLM l (T.stoneU t y))) :=
    ((T.resCLM l).continuous.tendsto _).comp (T.tendsto_stoneU t y)
  have heq : (fun k : ℕ => T.approxU ((k : ℝ) + 1) t (T.resCLM l y))
      = fun k : ℕ => T.resCLM l (T.approxU ((k : ℝ) + 1) t y) := by
    funext k
    exact congrArg (fun (S : H →L[ℂ] H) => S y) ((T.approxU_commute_resCLM ((k : ℝ) + 1) t l).eq)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

theorem stoneU_mem_domain (t : ℝ) (x : T.domain) : T.stoneU t (x : H) ∈ T.domain := by
  have hx : ((T.res 1 (T.shift 1 x) : T.domain) : H) = (x : H) := by
    rw [T.res_shift one_ne_zero]
  have h : T.stoneU t (x : H) = T.resCLM 1 (T.stoneU t (T.shift 1 x)) := by
    rw [← T.stoneU_commute_resCLM]
    congr 1
    exact hx.symm
  rw [h]
  exact T.resCLM_mem 1 _

end UnboundedSelfAdjoint
end BookProof.ChapterStoneResolvent


