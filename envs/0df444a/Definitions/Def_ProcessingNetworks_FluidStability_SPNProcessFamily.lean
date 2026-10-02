-- Prove2me | Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily
-- name    : ProcessingNetworks_FluidStability_SPNProcessFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:33:38.053817+00:00
-- url     : https://prove2.me/theorems/850e94c8-ab2a-499c-9e33-9cb1e41085d2
-- title:
--   Section 6.3: standard setup for the study of fluid limits
-- statement:
--   Section 6.3 sets up "many versions of a single SPN ... on a common probability space," one
--   per initial state $x$ of the ambient chain, sharing the same core stochastic elements (the
--   arrival process $E$ and the processing-variable sequences $v_j(\ell), \varphi_j(\ell)$ for
--   $\ell \ge 1$) but differing in the finite set $\Psi^x$ of initial processing variables, all
--   drawn from a single finite pool $\Pi_0$ independent of $(E, \Pi)$. This item packages the
--   resulting superscripted processes and the scaling apparatus of Section 6.4:
--
--   - `spnSize Mrep x` is $|x| := |z|:= \sum_i z_i$ where $z$ is the buffer-content component of
--     $f(x)$ (just before Eq. (6.37)).
--   - `UOCConverges f g` is convergence uniform on every compact interval $[0,T]$ ("u.o.c.",
--     Definition A.6), the mode of convergence in (6.39).
--   - `SPNProcessFamily` bundles, for every initial state $x$, the IP set $\Psi^x$ and the network
--     processes $S^x, F^x, N^x, T^x, D^x, Z^x$ of Chapter 2, required to satisfy the system relations
--     of Section 2.5 (mission I's `SPNRelations`: (2.7), (2.9), (2.10), (2.12), (2.31)–(2.34) and the
--     key relationship (6.51)) on the model data `sd` with initial data $(N^x(0), Z^x(0)) = f(x)$;
--     the uniform service-count bound $N^x_j(t) \le \kappa$ (6.35); the finite pool $\Pi_0$ from
--     which every IP pair is taken (so the stochastic bound (6.36) holds), independent of the core
--     stochastic elements; and the identification of the version for $x$ with the SPN started in $x$:
--     $Z^x(t)$ has the law of $Z(t)$ under $\Pr_x = \Pr(\,\cdot \mid X(0) = x)$, every state
--     carrying positive initial mass so that every $\Pr_x$ is defined. The fluid-equation data
--     `dat` carry the same $B$, $A$, $b$ as `sd`.
--   - `spnV` is $V^x_j(n,\omega)$ itself, Eq. (6.47): the sum of the residual service times of
--     the $N^x_j(0)$ already-open services, then as many of the post-time-zero service
--     times $v_j(1), v_j(2), \dots$ as are needed to reach $n$ terms in total (mission I's
--     `delayedWalk` for the IP set $\Psi^x$).
--
--   **Formalization note.** Chapter 2's construction of $(D^x, F^x, T^x, Z^x)$ from the primitive
--   stochastic elements by the policy mechanics is not re-derived: the family takes the processes as
--   given, constrained by exactly the relations the book's Section 2.5 recap and Section 6.3 setup
--   assert for them — which is what Lemmas 6.7–6.10 and Theorems 6.5, 6.2 actually use ((6.51) for
--   Lemma 6.8, (6.35)–(6.36) for Lemma 6.9, the system equations for Theorem 6.5, the law
--   identification $Z^x \sim Z \mid X(0) = x$ for the drift condition of Lemma 3.7 in Theorem 6.2).
--   The processes $D^x, F^x, Z^x$ are integer-valued as in the book, and are cast to $\mathbb{R}$ in
--   the fluid scaling (6.37).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 113-116, Section 6.3 and Eqs. (6.37), (6.47)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

/-- The scaling parameter `|x|` used throughout Section 6.4 (just before Eq. (6.37)): for a state
`x` of the ambient Markov chain with `f x = (n, z)`, `|x| := |z| := ∑ i, zᵢ`, the total buffer
content recorded by `x`. -/
noncomputable def spnSize {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J : ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (Mrep : MarkovRepresentation Xstate I J N Z) (x : Xstate) : ℝ :=
  ∑ i, ((Mrep.f x).2 i : ℝ)

/-- Uniform convergence on compact sets ("u.o.c.", Definition A.6, invoked at (6.39)): a sequence
of functions `f n : ℝ → Fin d → ℝ` converges to `g` uniformly on every interval `[0, T]`. -/
def UOCConverges {d : ℕ} (f : ℕ → ℝ → Fin d → ℝ) (g : ℝ → Fin d → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ t ∈ Set.Icc (0 : ℝ) T,
    ∀ i, |f n t i - g t i| < ε

/-- Section 6.3's "standard setup": many versions of one SPN on a common probability space, one
per initial state `x` of the ambient chain `Mrep`, all built by the policy mechanics of Chapter 2
from the shared core stochastic elements — the arrival process `E` and the post-time-zero
processing variables `(v, φ)` — together with an `x`-dependent IP set `Psi x` drawn from a single
finite pool `Π₀` of potential initial processing variables, independent of `(E, Π)`. For each `x`
the superscripted network processes `(S^x, F^x, N^x, T^x, D^x, Z^x)` satisfy the system relations
of Section 2.5 (`SPNRelations`, on the model data `sd`) with initial data `(N^x(0), Z^x(0)) =
f(x)`; the service counts are bounded uniformly in `x` (6.35); and the version for `x` is the SPN
started in state `x`: `Z^x(t)` has the law of `Z(t)` under `P_x = ℙ[|{X(0) = x}]` (every state
carrying positive initial mass, so that every `P_x` is defined). The fluid-equation data `dat`
carries the same `B`, `A`, `b` as `sd`. -/
structure SPNProcessFamily {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J K : ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (Mrep : MarkovRepresentation Xstate I J N Z) (sd : SPNData I J K)
    (dat : FluidEquationData I J K) (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ)
    (φ : Fin J → ℕ → Ω → Fin I → ℕ) : Type _ where
  data_B : dat.B = sd.B
  data_A : dat.A = sd.A
  data_b : dat.b = sd.b
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

/-- The `n`-step "delayed random walk" `V^x_j(n, ω)` of Eq. (6.47): the sum of the first `n`
type-`j` service times in the order of `L_j` — the residual service times of the `N^x_j(0)`
already-open services first, then the post-time-zero service times `v j 0, v j 1, …`
(mission I's `delayedWalk`, with the IP set `Psi x` of initial state `x`). -/
noncomputable def spnV {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J K : ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ)
    (x : Xstate) (j : Fin J) (n : ℕ) (ω : Ω) : ℝ :=
  delayedWalk (Mrep.f x).1 (fam.Psi x) v φ j n ω

end ProcessingNetworks.FluidStability


