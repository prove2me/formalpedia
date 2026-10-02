-- Prove2me | Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
-- name    : ProcessingNetworks_FluidEquations_ProcessFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:40:06.066179+00:00
-- url     : https://prove2.me/theorems/30f865ed-e725-4491-afab-7edf247b7308
-- title:
--   Fluid limit paths, restated (cf. mission III, Definition 6.6)
-- statement:
--   This mission's theorems, like mission III's, are all of the form "each fluid limit path of a
--   [specific policy] satisfies [an extra fluid equation]." Since drafts of this book's mission
--   series do not import one another's Lean files, this item restates mission III's apparatus:
--
--   - `UOCConverges f g`: $f_n \to g$ uniformly on every compact interval $[0,T]$ ("u.o.c.",
--     Definition A.6).
--   - `ProcessFamily`: Section 6.3's standard setup — for every initial state $x$ of the ambient
--     chain, the IP set $\Psi^x$ and the network processes $S^x, F^x, N^x, T^x, D^x, Z^x$ of Chapter
--     2, satisfying the system relations of Section 2.5 (mission I's `SPNRelations`: (2.7), (2.9),
--     (2.10), (2.12), (2.31)–(2.34) and the key relationship (6.51)) with $(N^x(0), Z^x(0)) = f(x)$;
--     the uniform service-count bound (6.35); a finite pool $\Pi_0$ of IP pairs independent of the
--     core stochastic elements $(E, \Pi)$ (the stochastic bound (6.36)); and the identification of the
--     version for $x$ with the SPN started in $x$, $Z^x(t) \sim Z(t) \mid X(0) = x$.
--   - `FluidLimitPath`: Definition 6.6, a four-tuple of continuous functions arising as a u.o.c.
--     limit of the fluid-scaled process family (6.37) along some sample point $\omega$ and sequence of
--     initial states $|x_n| \to \infty$, with $|x| = \sum_i z_i$ for $f(x) = (n, z)$ (mission I's
--     `MarkovRepresentation.size`).
--
--   **Formalization note.** This item is a restatement, not a new formalization: its content is
--   mission III's Section 6.3 setup and Definition 6.6. The processes $D^x, F^x, Z^x$ are
--   integer-valued as in the book and cast to $\mathbb{R}$ in the scaling (6.37). Carrying the full
--   setup (rather than four bare real processes) is what makes the chapter's theorems true: their
--   proofs use the system equations (Theorem 7.5's fluid-equations clause), the delayed random walk
--   and (6.36) (Theorem 7.3's remainder term), and the nonnegativity of $Z^x$ (Theorem 7.8).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 113-116, Section 6.3 and Definition 6.6 (restated)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel

namespace ProcessingNetworks.FluidEquations

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Uniform convergence on compact sets ("u.o.c.", Definition A.6, invoked at (6.39)): a sequence
of functions `f n : ℝ → Fin d → ℝ` converges to `g` uniformly on every interval `[0, T]`. Restated
from mission III (`ProcessingNetworks.FluidStability.UOCConverges`), since drafts of this series
do not import one another. -/
def UOCConverges {d : ℕ} (f : ℕ → ℝ → Fin d → ℝ) (g : ℝ → Fin d → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ t ∈ Set.Icc (0 : ℝ) T,
    ∀ i, |f n t i - g t i| < ε

/-- Section 6.3's standard setup, restated from mission III's `SPNProcessFamily`: many versions
of one SPN on a common probability space, one per initial state `x` of the ambient chain `Mrep`,
all built by the Chapter 2 mechanics from the shared core stochastic elements `E, v, φ` together
with an `x`-dependent IP set `Psi x` drawn from a single finite pool `Π₀` independent of
`(E, Π)`. For each `x` the superscripted network processes `(S^x, F^x, N^x, T^x, D^x, Z^x)`
satisfy the system relations of Section 2.5 (mission I's `SPNRelations`, on the model data `sd`)
with initial data `(N^x(0), Z^x(0)) = f(x)`; the service counts are bounded uniformly in `x`
(6.35); and the version for `x` is the SPN started in state `x`: `Z^x(t)` has the law of `Z(t)`
under `P_x = ℙ[|{X(0) = x}]`, every state carrying positive initial mass. -/
structure ProcessFamily {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J K : ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (Mrep : MarkovRepresentation Xstate I J N Z) (sd : SPNData I J K)
    (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ) :
    Type _ where
  Psi : Xstate → Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)
  S : Xstate → ℝ → Ω → Fin J → ℕ
  F : Xstate → ℝ → Ω → Fin J → ℕ
  Nx : Xstate → ℝ → Ω → Fin J → ℕ
  T : Xstate → ℝ → Ω → Fin J → ℝ
  D : Xstate → ℝ → Ω → Fin I → ℕ
  Zx : Xstate → ℝ → Ω → Fin I → ℕ
  relations : ∀ x, SPNRelations sd E v φ (Mrep.f x).1 (Psi x) (Mrep.f x).2
    (S x) (F x) (Nx x) (T x) (D x) (Zx x)
  service_bound : ∃ κ : ℕ, ∀ x (t : ℝ) ω j, Nx x t ω j ≤ κ
  pool : Finset (Ω → ℝ × (Fin I → ℕ))
  Psi_mem_pool : ∀ x j k, k < (Mrep.f x).1 j → (fun ω => Psi x j k ω) ∈ pool
  pool_indep :
    Indep (MeasurableSpace.comap (fun ω => fun p : {p // p ∈ pool} => p.1 ω) inferInstance)
      (MeasurableSpace.comap
        (fun ω => (fun i t => E i t ω, fun j ℓ => (v j ℓ ω, φ j ℓ ω))) inferInstance) ℙ
  initial_support : ∀ x, ℙ {ω | Mrep.X 0 ω = x} ≠ 0
  law : ∀ x (t : ℝ) (z : Fin I → ℕ), 0 ≤ t →
    ℙ {ω | Zx x t ω = z} = (ℙ[|{ω | Mrep.X 0 ω = x}]) {ω | Z t ω = z}

/-- Definition 6.6 (fluid limit path), restated (as `FluidLimitPath` was in mission III) for this
chapter's `ProcessFamily`: a four-tuple `(D̂, F̂, T̂, Ẑ)` of continuous functions is a fluid limit
path if there is a sample point `ω` and a sequence `{xₙ}` with `|xₙ| → ∞` (`|x| = Mrep.size x`,
Eq. (3.4)) along which the fluid-scaled processes (6.37) converge to it u.o.c. -/
def FluidLimitPath {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J K : ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep sd E v φ)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  Continuous Dh ∧ Continuous Fh ∧ Continuous Th ∧ Continuous Zh ∧
  ∃ (ω : Ω) (x : ℕ → Xstate), Tendsto (fun n => Mrep.size (x n)) atTop atTop ∧
    UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.D (x n) (Mrep.size (x n) * t) ω i : ℝ)) Dh ∧
    UOCConverges
      (fun n t j => (Mrep.size (x n))⁻¹ * (fam.F (x n) (Mrep.size (x n) * t) ω j : ℝ)) Fh ∧
    UOCConverges
      (fun n t j => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω j) Th ∧
    UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh

end ProcessingNetworks.FluidEquations


