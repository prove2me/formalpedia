-- Prove2me | Definitions.Def_StochApproxDyn_WeakAPT_Supplement_NormallyRepelling
-- name    : StochApproxDyn_WeakAPT_Supplement_NormallyRepelling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:12:54.844282+00:00
-- url     : https://prove2.me/theorems/480595be-3583-4807-950f-fbdac103c4d2
-- title:
--   §9 (corrected: tubular boundary) — normally repelling sets, C^{1+α} submanifolds and the transverse projection
-- statement:
--   These definitions set up §9 of the paper on $\mathbb R^m$ with the Euclidean norm.
--
--   1. A map $f$ is **$C^{1+\alpha}$** on a set $s$ ($0<\alpha\le1$) if it is $C^1$ there and its derivative is $\alpha$-Hölder near every point of $s$.
--   2. A set $S\subseteq\mathbb R^m$ is an embedded **$(m-d)$-dimensional submanifold** of class $C^r$ (resp. $C^{1+\alpha}$) if around each point of $S$ there is a chart $\varphi$, a $C^r$ (resp. $C^{1+\alpha}$) diffeomorphism between open subsets of $\mathbb R^m$, in which $S$ is the set where the last $d$ coordinates vanish. Its **tangent space** $T_pS$ is spanned by the velocities $c'(0)$ of curves with $c(0)=p$ that stay in $S$ near $0$. For complementary subspaces $V\oplus W=\mathbb R^m$, $\mathrm{proj}(V,W)$ is the projector onto $V$ along $W$.
--   3. **Standing assumptions of §9.** $F:\mathbb R^m\to\mathbb R^m$ generates the flow $\Phi$, $1\le d\le m$, and $\Gamma\subseteq S$ is a nonempty compact set with $\Phi_t(\Gamma)=\Gamma$ for all $t$. $S$ is **locally invariant**: there are a neighbourhood $U$ of $\Gamma$ and $t_0>0$ with $\Phi_t(U\cap S)\subseteq S$ for $|t|\le t_0$. For every $p\in\Gamma$, $\mathbb R^m=T_pS\oplus E^u_p$, where $p\mapsto E^u_p$ is continuous from $\Gamma$ into the Grassmannian $G(d,m)$, $D\Phi_t(p)E^u_p=E^u_{\Phi_t(p)}$ for all $t\in\mathbb R$, and there are $\lambda,C>0$ with
--   $$\|D\Phi_t(p)w\|\ge Ce^{\lambda t}\|w\|\qquad(p\in\Gamma,\ w\in E^u_p,\ t\ge0).$$
--   4. **The construction of §9.1, step 1.** With $f=\Phi_T$: $T>0$ and $\|Df(p)w\|\ge5\|w\|$ on $E^u$ over $\Gamma$; $N$ is a compact neighbourhood of $\Gamma$ with $N\subseteq U$, $f(N)\subseteq U$; $E^u$ extends continuously to $N$ with values in $G(d,m)$ and $\|Df(p)w\|\ge4\|w\|$ on it; $p\mapsto\tilde E^u_p$ is a $C^\infty$ map from $N$ into $G(d,m)$; $\varepsilon>0$ satisfies $\varepsilon(\|Df(p)\|+4)<1$ on $N$ and $\varepsilon\|Df(p)\|(\|P_p\|+\|\tilde P_p\|+1)<1$ on $N\cap S$, where $P_p$ and $\tilde P_p$ project onto $T_pS$ along $E^u_p$ and $\tilde E^u_p$; on $N\cap S$, $\mathbb R^m=T_pS\oplus E^u_p=T_pS\oplus\tilde E^u_p$ and $\|P_p-\tilde P_p\|\le\varepsilon$; finally $N_0\subseteq N$ is an open neighbourhood of $S\cap\operatorname{int}N$ and $\Pi:N_0\to S\cap N$ is the local inverse of $H(p,v)=p+v$ on the bundle $\tilde E^u$: $x=\Pi(x)+v$ with $v\in\tilde E^u_{\Pi(x)}$, this decomposition is locally unique, $\Pi$ is continuous, $\Pi=\mathrm{id}$ on $S\cap N_0$, and $D\Pi(p)=\tilde P_p$ for $p\in S\cap N_0$.
--   5. $V(x)=\|x-\Pi(x)\|$, $\eta(x)=\int_0^l V(\Phi_{-t}(x))\,dt$, and the **right derivative** $D\eta(x).h=\lim_{t\to0,t>0}(\eta(x+th)-\eta(x))/t$.
--
--   These objects carry the hypotheses of Theorem 9.1 (nonconvergence of Robbins–Monro algorithms to normally repelling sets) and the construction of the Lyapounov function in its proof (Lemma 9.3, Proposition 9.5).
--
--   **Formalization Note** Continuity and smoothness into $G(d,m)$ are expressed through the orthogonal projection onto the subspace. The construction is a predicate listing the properties the paper requires of its choices (Whitney embedding, Tietze extension and smoothing only serve to produce them), so the lemmas that use it hold for every admissible choice. The printed requirement "$N_0\subset N$ an open neighbourhood of $S\cap N$" cannot hold when $S$ meets the boundary of $N$; it is read as an open neighbourhood of $S\cap\operatorname{int}N$ inside $N$. The decomposition $\mathbb R^m=T_pS\oplus E^u_p$ on $N\cap S$, needed for $P_p$ to be defined, is part of the construction. In Lean the projection $\Pi$ is named `Pr` (`Π` is a reserved token).
--
--   Differences from the source:
--   - generalization: smooth/global Hölder data → regularity supplied by each theorem, with local Hölder bounds; reason: the source cases specialize to these predicates.
--   - correction: the open $N_0\subseteq N$ containing $S\cap N$ → $S\cap\operatorname{int}N\subseteq N_0\subseteq N$; reason: an ambient open subset of $N$ cannot contain its boundary points; the inverse construction is local around $\Gamma$.
--   - encoding: the inverse of $H(p,v)=p+v$ → continuity, locally unique transverse decompositions, identity on $S$ and its specified derivative; reason: these fix the same local inverse. Projectors default to zero only outside the complementary case, and a right derivative is used only with its existence asserted.
--   - correction: §9(ii) prints $p\in E_p^u$ for a base point → $p\in\Gamma$; reason: the preceding sentence defines the splitting over every $p\in\Gamma$, and the fiber vectors are $w$ in (iii).
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), pp. 47–48, §9 (standing assumptions); p. 49 (C^{1+α}); pp. 50–51, §9.1 step 1 (construction of T, N, Ẽ^u, ε, N₀, Π, V); p. 52 (right derivative); p. 53, Proposition 9.5 (η)

import Mathlib

namespace StochApproxDyn.WeakAPT.Supplement

open scoped NNReal Topology ContDiff
open Filter

/-- A map `f` is `C^{1+α}` on `s` (Benaïm 1999, §9, p. 49: "`C¹` and its derivative is
`α`-Hölder"): `f` is `C¹` on `s` and its derivative is `α`-Hölder near every point of `s`. -/
def IsC1HolderOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ≥0) (f : E → F) (s : Set E) : Prop :=
  ContDiffOn ℝ 1 f s ∧ ∀ x ∈ s, ∃ W ∈ 𝓝 x, ∃ C : ℝ≥0, HolderOnWith C α (fderiv ℝ f) (W ∩ s)

/-- `φ` is a slice chart of `S ⊆ ℝ^m` for an `(m − d)`-dimensional submanifold: inside the
chart domain, `S` is the set where the last `d` coordinates of `φ` vanish (0-based indices
`m − d, …, m − 1`). -/
def IsSliceChart {m : ℕ} (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin m)))
    (φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))) : Prop :=
  S ∩ φ.source = {x ∈ φ.source | ∀ i : Fin m, m - d ≤ i.val → φ x i = 0}

/-- `S ⊆ ℝ^m` is an embedded `(m − d)`-dimensional submanifold of class `C^r` (`d ≤ m`): every
point of `S` lies in the domain of a slice chart which is a `C^r` diffeomorphism between open
subsets of `ℝ^m`. -/
def IsSubmanifoldOfClass {m : ℕ} (r : ℕ∞) (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  d ≤ m ∧ ∀ p ∈ S, ∃ φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m)), p ∈ φ.source ∧ IsSliceChart d S φ ∧
    ContDiffOn ℝ (r : WithTop ℕ∞) φ φ.source ∧ ContDiffOn ℝ (r : WithTop ℕ∞) φ.symm φ.target

/-- `S ⊆ ℝ^m` is an embedded `(m − d)`-dimensional `C^{1+α}` submanifold (p. 49: "a manifold
whose transition functions may be chosen `C^{1+α}`"): every point of `S` lies in the domain of a
slice chart which, with its inverse, is `C^{1+α}`. -/
def IsC1HolderSubmanifold {m : ℕ} (α : ℝ≥0) (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))) :
    Prop :=
  d ≤ m ∧ ∀ p ∈ S, ∃ φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m)), p ∈ φ.source ∧ IsSliceChart d S φ ∧
    IsC1HolderOn α φ φ.source ∧ IsC1HolderOn α φ.symm φ.target

/-- The tangent space `T_p S` of a set `S ⊆ ℝ^m` at `p`, as the span of the velocities `c'(0)`
of curves `c` with `c(0) = p` that stay in `S` near `t = 0`. For an embedded `C¹`
submanifold this is its tangent space at `p`. -/
def tangentSubspace {m : ℕ} (S : Set (EuclideanSpace ℝ (Fin m)))
    (p : EuclideanSpace ℝ (Fin m)) : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ {v | ∃ c : ℝ → EuclideanSpace ℝ (Fin m), c 0 = p ∧
    (∀ᶠ t in 𝓝 0, c t ∈ S) ∧ HasDerivAt c v 0}

/-- The projector `ℝ^m = V ⊕ W → V`, `v + w ↦ v`, onto `V` along `W`, as a map `ℝ^m → ℝ^m`
(defined as `0` when `V` and `W` are not complementary, a case never used). -/
noncomputable def projAlong {m : ℕ} (V W : Submodule ℝ (EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  open Classical in
  if h : IsCompl V W then
    LinearMap.toContinuousLinearMap (V.subtype ∘ₗ Submodule.projectionOnto V W h)
  else 0

/-- The standing assumptions of §9 (Benaïm 1999, pp. 47–48), without the regularity of `F` and
`S` (which each result states). `F : ℝ^m → ℝ^m` generates the flow `Φ`
(`d/dt Φ_t(x) = F(Φ_t(x))`); `S ⊆ ℝ^m` is the `(m − d)`-dimensional submanifold, `1 ≤ d ≤ m`;
`Γ ⊆ S` is nonempty, compact and invariant (`Φ_t(Γ) = Γ` for all `t ∈ ℝ`); `S` is locally
invariant: `Φ_t(U ∩ S) ⊆ S` for `|t| ≤ t₀`, where `U` is a neighbourhood of `Γ` and `t₀ > 0`; and
for every `p ∈ Γ`, `ℝ^m = T_p S ⊕ E^u_p` where
(i) `p ↦ E^u_p` is continuous from `Γ` into the Grassmannian `G(d, m)` (continuity of the
orthogonal projection onto `E^u_p`, each `E^u_p` of dimension `d`),
(ii) `DΦ_t(p) E^u_p = E^u_{Φ_t(p)}` for all `t ∈ ℝ`, `p ∈ Γ`,
(iii) there are `λ > 0`, `C > 0` with `‖DΦ_t(p) w‖ ≥ C e^{λ t} ‖w‖` for `p ∈ Γ`, `w ∈ E^u_p`,
`t ≥ 0`. -/
def IsNormallyRepellingSet {m : ℕ} (d : ℕ)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (Φ : Flow ℝ (EuclideanSpace ℝ (Fin m))) (S Γ U : Set (EuclideanSpace ℝ (Fin m))) (t₀ : ℝ)
    (Eu : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
  (∀ x t, HasDerivAt (fun s => Φ s x) (F (Φ t x)) t) ∧
  1 ≤ d ∧ d ≤ m ∧
  Γ.Nonempty ∧ IsCompact Γ ∧ Γ ⊆ S ∧ (∀ t : ℝ, Φ t '' Γ = Γ) ∧
  U ∈ 𝓝ˢ Γ ∧ 0 < t₀ ∧ (∀ t : ℝ, |t| ≤ t₀ → Φ t '' (U ∩ S) ⊆ S) ∧
  (∀ p ∈ Γ, IsCompl (tangentSubspace S p) (Eu p) ∧ Module.finrank ℝ (Eu p) = d) ∧
  ContinuousOn (fun p => (Eu p).starProjection) Γ ∧
  (∀ t : ℝ, ∀ p ∈ Γ, (Eu p).map (fderiv ℝ (Φ t) p : _ →ₗ[ℝ] _) = Eu (Φ t p)) ∧
  ∃ lam C : ℝ, 0 < lam ∧ 0 < C ∧ ∀ p ∈ Γ, ∀ w ∈ Eu p, ∀ t : ℝ, 0 ≤ t →
    C * Real.exp (lam * t) * ‖w‖ ≤ ‖fderiv ℝ (Φ t) p w‖

/-- The construction of §9.1, step 1 (Benaïm 1999, pp. 50–51), as the list of properties the
paper requires of its choices. With `f = Φ_T` and `Df(p) = DΦ_T(p)`:
1. `T > 0` and `‖Df(p) w‖ ≥ 5‖w‖` for `p ∈ Γ`, `w ∈ E^u_p`;
2. `N` is a compact neighbourhood of `Γ` with `N ⊆ U` and `f(N) ⊆ U`;
3. `p ↦ E^u_p` (`Eext`) is a continuous extension to `N` with values in `G(d, m)`, equal to `E^u`
on `Γ`, with `‖Df(p) w‖ ≥ 4‖w‖` for `p ∈ N`, `w ∈ E^u_p`;
4. `p ↦ Ẽ^u_p` (`Et`) is a `C^∞` map from `N` into `G(d, m)`;
5. `ε > 0` with `ε(‖Df(p)‖ + 4) < 1` for `p ∈ N` and `ε‖Df(p)‖(‖P_p‖ + ‖P̃_p‖ + 1) < 1` for
`p ∈ N ∩ S`, where `P_p` projects onto `T_p S` along `E^u_p` and `P̃_p` onto `T_p S` along
`Ẽ^u_p`;
6. for `p ∈ N ∩ S`: `ℝ^m = T_p S ⊕ E^u_p` (so that `P_p` is defined), `ℝ^m = T_p S ⊕ Ẽ^u_p`,
and `‖P_p − P̃_p‖ ≤ ε`;
7. `N₀ ⊆ N` is an open neighbourhood of `S ∩ int N` and `Π : N₀ → S ∩ N` is the inverse of
`H(p, v) = p + v` on the bundle `Ẽ^u` near its zero section: for `x ∈ N₀`,
`x = Π(x) + v` with `v ∈ Ẽ^u_{Π(x)}`, `(Π(x), x − Π(x))` is the only such decomposition near
itself, `Π` is continuous on `N₀`, `Π(p) = p` on `S ∩ N₀`, and `DΠ(p) = P̃_p` for `p ∈ N₀ ∩ S`.
The Lyapounov-type function is then `V(x) = ‖x − Π(x)‖` on `N₀`. -/
def IsTubularConstruction {m : ℕ} (d : ℕ) (Φ : Flow ℝ (EuclideanSpace ℝ (Fin m)))
    (S Γ U : Set (EuclideanSpace ℝ (Fin m)))
    (Eu : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (T : ℝ)
    (N : Set (EuclideanSpace ℝ (Fin m)))
    (Eext Et : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (N₀ : Set (EuclideanSpace ℝ (Fin m)))
    (Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) : Prop :=
  -- 1.
  (0 < T ∧ ∀ p ∈ Γ, ∀ w ∈ Eu p, 5 * ‖w‖ ≤ ‖fderiv ℝ (Φ T) p w‖) ∧
  -- 2.
  (IsCompact N ∧ N ∈ 𝓝ˢ Γ ∧ N ⊆ U ∧ Φ T '' N ⊆ U) ∧
  -- 3.
  (ContinuousOn (fun p => (Eext p).starProjection) N ∧ (∀ p ∈ N, Module.finrank ℝ (Eext p) = d) ∧
    (∀ p ∈ Γ, Eext p = Eu p) ∧ ∀ p ∈ N, ∀ w ∈ Eext p, 4 * ‖w‖ ≤ ‖fderiv ℝ (Φ T) p w‖) ∧
  -- 4.
  ((∀ p ∈ N, Module.finrank ℝ (Et p) = d) ∧ ContDiffOn ℝ ∞ (fun p => (Et p).starProjection) N) ∧
  -- 5.
  (0 < ε ∧ (∀ p ∈ N, ε * (‖fderiv ℝ (Φ T) p‖ + 4) < 1) ∧
    ∀ p ∈ N ∩ S, ε * ‖fderiv ℝ (Φ T) p‖ *
      (‖projAlong (tangentSubspace S p) (Eext p)‖ + ‖projAlong (tangentSubspace S p) (Et p)‖ + 1)
        < 1) ∧
  -- 6.
  (∀ p ∈ N ∩ S, IsCompl (tangentSubspace S p) (Eext p) ∧ IsCompl (tangentSubspace S p) (Et p) ∧
    ‖projAlong (tangentSubspace S p) (Eext p) - projAlong (tangentSubspace S p) (Et p)‖ ≤ ε) ∧
  -- 7.
  (IsOpen N₀ ∧ S ∩ interior N ⊆ N₀ ∧ N₀ ⊆ N ∧ ContinuousOn Pr N₀ ∧
    (∀ x ∈ N₀, Pr x ∈ S ∩ N ∧ x - Pr x ∈ Et (Pr x) ∧
      ∃ W ∈ 𝓝 (Pr x, x - Pr x), ∀ q v, (q, v) ∈ W → q ∈ S ∩ N → v ∈ Et q → q + v = x →
        q = Pr x) ∧
    (∀ p ∈ S ∩ N₀, Pr p = p) ∧
    ∀ p ∈ S ∩ N₀, HasFDerivAt Pr (projAlong (tangentSubspace S p) (Et p)) p)

/-- `V(x) = ‖x − Π(x)‖` (p. 51), the distance from `x` to its base point `Π(x) ∈ S`. -/
noncomputable def tubeDist {m : ℕ} (Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ‖x - Pr x‖

/-- `η(x) = ∫_0^l V(Φ_{−t}(x)) dt` (Proposition 9.5, p. 53). -/
noncomputable def etaFun {m : ℕ} (Φ : Flow ℝ (EuclideanSpace ℝ (Fin m)))
    (Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (l : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ t in (0 : ℝ)..l, tubeDist Pr (Φ (-t) x)

/-- The right derivative `Dη(x).h = lim_{t → 0, t > 0} (η(x + t h) − η(x))/t` (p. 52), as a
value (meaningful where the limit exists). -/
noncomputable def rightDirDeriv {m : ℕ} (η : EuclideanSpace ℝ (Fin m) → ℝ)
    (x h : EuclideanSpace ℝ (Fin m)) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun t => (η (x + t • h) - η x) / t)

/-- `η` admits a right derivative at `x` (p. 52): for every `h ∈ ℝ^m` the limit
`lim_{t → 0, t > 0} (η(x + t h) − η(x))/t` exists (and is `rightDirDeriv η x h`). -/
def HasRightDirDerivAt {m : ℕ} (η : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ h, Tendsto (fun t : ℝ => (η (x + t • h) - η x) / t) (𝓝[>] 0) (𝓝 (rightDirDeriv η x h))

end StochApproxDyn.WeakAPT.Supplement


