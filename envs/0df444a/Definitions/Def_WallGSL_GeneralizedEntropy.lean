-- Prove2me | Definitions.Def_WallGSL_GeneralizedEntropy
-- name    : WallGSL_GeneralizedEntropy
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T17:51:51.172298+00:00
-- url     : https://prove2.me/theorems/f9c1f83d-1e84-4867-bdfd-b758f0d9e7b4
-- title:
--   Generalized entropy, fine-grained GSL and quantum trapped surfaces
-- statement:
--   This definition file encodes the thermodynamic notions of Wall (2013): the generalized entropy, the fine-grained generalized second law, the semiclassical comparison principle of Theorem 1, and quantum trapped surfaces. It builds on `WallGSL_Spacetime`.
--
--   The fine-grained generalized entropy $S_{\rm gen}=A/4\hbar G+Q+S_{\rm out}$ has no rigorous definition, so it is an **arbitrary function** $S_{\rm gen}:\mathcal P(M)\to\mathbb R$, read as the generalized entropy of (the part of a slice lying in) a region.
--
--   1. **Forward deformation.** $\Sigma'$ is obtained from a Cauchy surface $\Sigma$ by pushing it forwards inside $U$ if $\Sigma'$ is a Cauchy surface, $\Sigma'\setminus U=\Sigma\setminus U$, and $\Sigma'\subseteq J^+(\Sigma)$.
--   2. **Decreasing generalized entropy at $g_0$** (Theorem 3's sense) of an exterior region $X$: there is a Cauchy surface $\Sigma\ni g_0$ such that for every neighbourhood $U$ of $g_0$ there is a forward deformation $\Sigma'$ of $\Sigma$ inside $U$ with $S_{\rm gen}(\Sigma'\cap X)<S_{\rm gen}(\Sigma\cap X)$.
--   3. **Observer:** a future-infinite timelike worldline, or a future-infinite null ray (§2.2).
--   4. **Fine-grained GSL** (eq. (10)): for every observer $W$ and Cauchy surfaces $\Sigma,\Sigma'$ with $\Sigma'\subseteq J^+(\Sigma)$,
--   $$S_{\rm gen}(\Sigma\cap I^-(W))\le S_{\rm gen}(\Sigma'\cap I^-(W)).$$
--   5. **Theorem 1 comparison at $g_0$** for a null surface $N$ with exterior $X$: whenever an observer's horizon $H=\partial I^-(W)$ satisfies $N\cap I^-(W)=\emptyset$ and a future-directed null geodesic segment starting at $g_0$ lies on $N\cap H$, decreasing generalized entropy of $X$ at $g_0$ implies decreasing generalized entropy of $I^-(W)$ at $g_0$.
--   6. **Outgoing null surface** of $T=\partial_\Sigma\mathrm{Ext}$: $N=\big(\partial I^+(\Sigma\setminus\mathrm{Ext})\setminus(\Sigma\setminus\mathrm{Ext})\big)\cup T$, with exterior $\big(\overline{I^+(\Sigma\setminus\mathrm{Ext})}\big)^{c}$.
--   7. **Quantum trapped surface** (§3.2): $\Sigma$ is a connected Cauchy surface, $\mathrm{Ext}\subseteq\Sigma$ is relatively open with noncompact closure, $T=(\overline{\mathrm{Ext}}\cap\Sigma)\setminus\mathrm{Ext}$ is nonempty and compact, and the generalized entropy of the exterior of $N$ is decreasing at every $g_0\in T$.
--
--   **Formalization Note** Item 5 is the formal stand-in for "the semiclassical approximation is valid near $g_0$": in the paper the comparison is derived (Theorem 1) from the semiclassical expansion, which has no rigorous formulation. "Decreasing" is strict, unlike the $\le$ in eq. (33), because with $\le$ a constant $S_{\rm gen}$ would count as decreasing everywhere while satisfying the GSL.
-- source:
--   A. C. Wall, The generalized second law implies a quantum singularity theorem, Class. Quantum Grav. 30 (2013) 165003, https://doi.org/10.1088/0264-9381/30/16/165003, §2.2 eq. (10) (GSL, p. 6), Theorem 1 (p. 9), Theorem 3 eq. (33) (p. 14), quantum trapped surface definition (p. 15)

import Definitions.Def_WallGSL_Spacetime

/-!
# Generalized entropy, the generalized second law, and quantum trapped surfaces

Definition layer (part 2) for the formalization of
A. C. Wall, *The generalized second law implies a quantum singularity theorem*,
Class. Quantum Grav. 30 (2013) 165003, §2.2 and §3.

The fine-grained generalized entropy `S_gen = A/(4ħG) + Q + S_out` of the paper has no
rigorous mathematical definition, so it is modelled abstractly as an arbitrary function
`Sgen : Set M → ℝ` assigning a generalized entropy to (the part of a time slice lying in)
a region of spacetime.  All physical input about it enters through explicit hypotheses:
the fine-grained GSL (eq. (10)) and, near the relevant points, the comparison principle
of Theorem 1 (which is the paper's consequence of the semiclassical approximation).
-/

open scoped Manifold Topology ContDiff
open Set Filter

namespace WallGSL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

namespace LorentzianMetric

variable (st : LorentzianMetric E M)

/-- `S'` is obtained from the Cauchy surface `S` by pushing it forwards in time inside
`U`: `S'` is again a Cauchy surface, it agrees with `S` outside `U`, and it lies in the
causal future of `S` ("nowhere to the past of `S`"). -/
def IsForwardDeformation (S S' U : Set M) : Prop :=
  st.IsCauchySurface S' ∧ S' \ U = S \ U ∧ S' ⊆ st.causalFuture S

/-- The generalized entropy of the exterior region `X` (of some null surface) is
decreasing at the point `g₀`, in the sense of Theorem 3 of the paper: there is a Cauchy
surface `S` through `g₀` such that, for every neighbourhood `U` of `g₀`, `S` can be pushed
forwards in time inside `U` to a Cauchy surface `S'` with
`Sgen (S' ∩ X) < Sgen (S ∩ X)`. -/
def EntropyDecreasingAt (Sgen : Set M → ℝ) (X : Set M) (g₀ : M) : Prop :=
  ∃ S : Set M, st.IsCauchySurface S ∧ g₀ ∈ S ∧
    ∀ U ∈ 𝓝 g₀, ∃ S' : Set M, st.IsForwardDeformation S S' U ∧ Sgen (S' ∩ X) < Sgen (S ∩ X)

/-- An "observer" in the sense of §2.2 of the paper, starting at parameter `a`: either a
future-infinite timelike worldline, or a future-directed null ray whose affine parameter
is infinite to the future. -/
def IsFutureObserver (W : ℝ → M) (a : ℝ) : Prop :=
  st.IsFutureInfiniteTimelike W a ∨ st.IsFutureInfiniteNullRay W a

/-- The fine-grained generalized second law, eq. (10) of the paper: for every observer
`W` with future causal horizon `∂I⁻(W)` and every pair of Cauchy surfaces `S, S'` with
`S'` nowhere to the past of `S`, the generalized entropy of the exterior `I⁻(W)` does not
decrease: `Sgen (S ∩ I⁻(W)) ≤ Sgen (S' ∩ I⁻(W))`. -/
def FineGrainedGSL (Sgen : Set M → ℝ) : Prop :=
  ∀ (W : ℝ → M) (a : ℝ), st.IsFutureObserver W a →
    ∀ S S' : Set M, st.IsCauchySurface S → st.IsCauchySurface S' →
      S' ⊆ st.causalFuture S →
      Sgen (S ∩ st.chronPast (W '' Ici a)) ≤ Sgen (S' ∩ st.chronPast (W '' Ici a))

/-- The comparison principle of Theorem 1 at the point `g₀`, for the null surface `N` with
exterior `X` (the inner surface) against causal horizons (the outer surface): whenever an
observer `W` has a causal horizon `H = ∂I⁻(W)` such that `N` lies within or on `H`
(`N ∩ I⁻(W) = ∅`) and some future-directed null geodesic segment starting at `g₀` lies on
both `N` and `H`, then decreasing generalized entropy of `X` at `g₀` forces decreasing
generalized entropy of the exterior `I⁻(W)` of `H` at `g₀`.

In the paper this is the content of Theorem 1, derived from the semiclassical
approximation near `g₀`; here it is the formal stand-in for "the semiclassical
approximation is valid near `g₀`". -/
def TheoremOneComparisonAt (Sgen : Set M → ℝ) (N X : Set M) (g₀ : M) : Prop :=
  ∀ (W : ℝ → M) (a : ℝ), st.IsFutureObserver W a →
    N ∩ st.chronPast (W '' Ici a) = ∅ →
    (∃ (γ : ℝ → M) (s b : ℝ), s < b ∧ γ s = g₀ ∧ ContinuousWithinAt γ (Ici s) s ∧
      st.IsGeodesicOn γ (Ioo s b) ∧ (∀ t ∈ Ioo s b, st.IsFutureNull (γ t) (velocity γ t)) ∧
      γ '' Ico s b ⊆ N ∩ frontier (st.chronPast (W '' Ici a))) →
    st.EntropyDecreasingAt Sgen X g₀ →
    st.EntropyDecreasingAt Sgen (st.chronPast (W '' Ici a)) g₀

/-- The null surface `N` shot out from `T` outwards and to the future, where `T` is the
boundary in the Cauchy surface `S` of the exterior region `Ext ⊆ S`: it consists of `T`
together with the part of the boundary of the chronological future of the inner closed
region `S \ Ext` that lies off `S \ Ext`. -/
def outgoingNullSurface (S T Ext : Set M) : Set M :=
  (frontier (st.chronFuture (S \ Ext)) \ (S \ Ext)) ∪ T

/-- The exterior side of the outgoing null surface: the complement of the closure of the
chronological future of the inner region `S \ Ext`. -/
def outgoingExterior (S Ext : Set M) : Set M :=
  (closure (st.chronFuture (S \ Ext)))ᶜ

/-- A quantum trapped surface (§3.2 of the paper).  `S` is a connected Cauchy surface,
`Ext ⊆ S` is a relatively open subset of `S` whose closure is noncompact (the exterior of
`T` on `S` is noncompact), and `T` is its relative boundary in `S`, assumed nonempty and
compact.  Finally, for every point `g₀ ∈ T` the fine-grained generalized entropy of the
exterior of the outgoing null surface shot out from `T` is decreasing at `g₀`, in the
sense of Theorem 3. -/
structure IsQuantumTrappedSurface (Sgen : Set M → ℝ) (S T Ext : Set M) : Prop where
  cauchy : st.IsCauchySurface S
  connected : IsConnected S
  ext_subset : Ext ⊆ S
  ext_relOpen : ∃ V : Set M, IsOpen V ∧ Ext = V ∩ S
  ext_noncompact : ¬ IsCompact (closure Ext)
  boundary_eq : T = (closure Ext ∩ S) \ Ext
  nonempty : T.Nonempty
  compact : IsCompact T
  decreasing : ∀ g₀ ∈ T, st.EntropyDecreasingAt Sgen (st.outgoingExterior S Ext) g₀

end LorentzianMetric

end WallGSL


