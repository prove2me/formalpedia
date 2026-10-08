-- Prove2me | Definitions.Def_HarmonicGames_Decomposition_Games
-- name    : HarmonicGames_Decomposition_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:52.266129+00:00
-- url     : https://prove2.me/theorems/cbb200f9-19fd-4e2f-ada4-cdebaa23b4c0
-- title:
--   Games as flows on the game graph: D_m, D, Δ_{0,m}, Π_m, Π, ν, normalized games, the subspaces P, H, N and the components of Theorem 4.1
-- statement:
--   A finite game has a finite set of players $\mathcal M$ and, for each player $m$, a finite nonempty strategy set $E^m$ with $h_m = |E^m|$ elements. A strategy profile is $p = (p^m)_{m\in\mathcal M} \in E = \prod_m E^m$; $p^{-m}$ denotes the strategies of the players other than $m$, and $(q^m, p^{-m})$ the profile $p$ with player $m$'s strategy replaced by $q^m$. A game is a collection of utilities $u = (u^m)_{m \in \mathcal M}$ with $u^m \in C_0 = \{E \to \mathbb R\}$, so the space of games is $\mathcal G_{\mathcal M,E} \cong C_0^{\mathcal M}$.
--
--   1. Profiles $p, q$ are **$m$-comparable** if $p \ne q$ and they differ only in player $m$'s strategy. The **game graph** has the profiles as nodes and an edge between comparable profiles (comparable = $m$-comparable for some $m$). $W^m(p,q)$ is the indicator of $m$-comparability.
--   2. $D_m : C_0 \to C_1$, $(D_m\varphi)(p,q) = W^m(p,q)(\varphi(q) - \varphi(p))$ (20), where $C_1$ is the edge-flow space of the game graph with the inner product (7).
--   3. $D : C_0^{\mathcal M} \to C_1$, $Du = \sum_m D_m u^m$ (21). $C_0^{\mathcal M}$ carries the inner product $\langle u, v\rangle = \sum_m \langle u^m, v^m\rangle_0$ (p. 14).
--   4. $\Delta_{0,m} = D_m^* D_m$, $\Pi_m = D_m^\dagger D_m$ and $\Pi = \operatorname{diag}(\Pi_1,\dots,\Pi_M)$, i.e. $(\Pi u)^m = \Pi_m u^m$.
--   5. For $q^{-m} \in E^{-m}$, $\nu_{q^{-m}} \in C_0$ with $\nu_{q^{-m}}(p) = 1$ if $p^{-m} = q^{-m}$ and $0$ otherwise (26).
--   6. **Definition 4.1.** A game is **normalized** if $\sum_{p^m \in E^m} u^m(p^m, p^{-m}) = 0$ for all $p^{-m} \in E^{-m}$ and all $m$ (27).
--   7. **Definition 4.2.** With $\delta_0$ the gradient of the game graph,
--   $$
--   \begin{aligned}
--   \mathcal P &= \{u \in C_0^{\mathcal M} \mid u = \Pi u \text{ and } Du \in \operatorname{im}\delta_0\},\\
--   \mathcal H &= \{u \in C_0^{\mathcal M} \mid u = \Pi u \text{ and } Du \in \ker\delta_0^*\},\\
--   \mathcal N &= \{u \in C_0^{\mathcal M} \mid u \in \ker D\}.
--   \end{aligned}
--   $$
--   8. The maps of Theorem 4.1: $u_P = D^\dagger\delta_0\delta_0^\dagger D u$, $u_H = D^\dagger(I - \delta_0\delta_0^\dagger)Du$, $u_N = (I - D^\dagger D)u$, and $\varphi = \delta_0^\dagger D u$.
--
--   These are the objects of the paper's decomposition of a game into potential, harmonic and nonstrategic components.
--
--   **Formalization Note** Players form a `Fintype` `ι`; strategy sets are `E : ι → Type` with `Fintype` and `DecidableEq` instances (nonemptiness is assumed in the theorems, not needed here). The space of games is `PiLp 2 (fun _ : ι => C0)`, whose inner product is the unweighted sum above; all pseudoinverses ($D_m^\dagger$, $D^\dagger$, $\delta_0^\dagger$) are taken for these inner products and the $\tfrac12$-inner product on $C_1$. $(q^m, p^{-m})$ is `Function.update p m q`, so the normalization sums over the $m$-th coordinate of a full profile $p$; the index $q^{-m}$ of $\nu$ is a function on the players $k \ne m$. $\mathcal P$, $\mathcal H$ are written as the intersection of the fixed-point set of $\Pi$ with the preimage under $D$ of $\operatorname{im}\delta_0$, resp. $\ker\delta_0^*$, exactly (28); they are not defined through the component maps.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, pp. 5–6 (§2.1–2.2), pp. 12–17 (§4.1–4.2, eqs. (20), (21), (26)–(28), Table 1, Definitions 4.1 and 4.2, Theorem 4.1)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows

/-!
Finite games as flows on the game graph (Sections 2.1, 2.2 and 4.1 of Candogan, Menache,
Ozdaglar, Parrilo): the game graph, the operators `D_m` (20) and `D` (21), the Laplacians
`Δ_{0,m}`, the projections `Π_m = D_m† D_m` and `Π = diag(Π_1, …, Π_M)`, the kernel basis
vectors `ν_{q^{-m}}` (26), normalized games (Definition 4.1), and the potential, harmonic and
nonstrategic subspaces `P`, `H`, `N` (Definition 4.2, (28)).
-/

noncomputable section

namespace HarmonicGames.Decomposition

open scoped InnerProductSpace

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

/-- Strategy profiles `p : ∀ m, E m` and `q` are **`m`-comparable** if they differ, and differ
only in the strategy of player `m`: `p ≠ q` and `p k = q k` for every `k ≠ m`. -/
def MComparable (m : ι) (p q : ∀ k, E k) : Prop := p ≠ q ∧ ∀ k, k ≠ m → p k = q k

instance (m : ι) (p q : ∀ k, E k) : Decidable (MComparable E m p q) := by
  unfold MComparable; infer_instance

/-- The graph `(E, A^m)` of `m`-comparable strategy profiles. -/
def mGraph (m : ι) : SimpleGraph (∀ k, E k) where
  Adj := MComparable E m
  symm := ⟨fun _ _ h => ⟨fun e => h.1 e.symm, fun k hk => (h.2 k hk).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (m : ι) : DecidableRel (mGraph E m).Adj := fun p q =>
  inferInstanceAs (Decidable (MComparable E m p q))

/-- The **game graph** `G(G) = (E, A)` (Section 2.2): nodes are strategy profiles, and `p, q`
are adjacent iff they are comparable, i.e. `m`-comparable for some player `m`. -/
def gameGraph : SimpleGraph (∀ k, E k) where
  Adj p q := ∃ m, MComparable E m p q
  symm := ⟨fun _ _ ⟨m, h⟩ => ⟨m, fun e => h.1 e.symm, fun k hk => (h.2 k hk).symm⟩⟩
  loopless := ⟨fun _ ⟨_, h⟩ => h.1 rfl⟩

instance : DecidableRel (gameGraph E).Adj := fun p q =>
  inferInstanceAs (Decidable (∃ m, MComparable E m p q))

theorem mGraph_le_gameGraph (m : ι) : mGraph E m ≤ gameGraph E := fun _ _ h => ⟨m, h⟩

/-- `C0 = {f : E → ℝ}` on strategy profiles. -/
abbrev Util := C0 (∀ k, E k)

/-- The space of edge flows on the game graph. -/
abbrev Flow := C1 (gameGraph E)

/-- The indicator `W^m(p,q)` of `m`-comparability. -/
def Wm (m : ι) (p q : ∀ k, E k) : ℝ := if MComparable E m p q then 1 else 0

/-- `D_m : C0 → C1` of (20): `(D_m φ)(p,q) = W^m(p,q) (φ(q) - φ(p))`. -/
def Dm (m : ι) : Util E →ₗ[ℝ] Flow E :=
  gradOn (gameGraph E) (mGraph E m) (mGraph_le_gameGraph E m)

/-- The space of games `G_{M,E} ≅ C0^M`, `u = (u^m)_{m ∈ M}`, with the inner product
`⟨u, v⟩ = ∑_m ⟨u^m, v^m⟩₀` (the sum of the inner products of the `C0` components, p. 14). -/
abbrev Games := PiLp 2 (fun _ : ι => Util E)

/-- `D : C0^M → C1` of (21): `D u = ∑_m D_m u^m`, the flow (pairwise comparisons) of the
game `u`. -/
def Dop : Games E →ₗ[ℝ] Flow E where
  toFun u := ∑ m, Dm E m (u m)
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.smul_sum]

/-- The Laplacian `Δ_{0,m} = D_m* D_m : C0 → C0` of the graph of `m`-comparable profiles,
with `D_m*` the adjoint for the inner products (7). -/
def Delta0m (m : ι) : Util E →ₗ[ℝ] Util E := LinearMap.adjoint (Dm E m) ∘ₗ Dm E m

/-- `Π_m = D_m† D_m : C0 → C0`, with `D_m†` the Moore–Penrose pseudoinverse for the inner
products (7). -/
def Pim (m : ι) : Util E →ₗ[ℝ] Util E := pinv (Dm E m) ∘ₗ Dm E m

/-- `Π = diag(Π_1, …, Π_M) : C0^M → C0^M`, `(Π u)^m = Π_m u^m`. -/
def PiOp : Games E →ₗ[ℝ] Games E where
  toFun u := WithLp.toLp 2 (fun m => Pim E m (u m))
  map_add' u v := by ext m p; simp
  map_smul' c u := by ext m p; simp

/-- The vector `ν_{q^{-m}} ∈ C0` of (26), indexed by a strategy profile `q^{-m}` of the players
other than `m`: `ν_{q^{-m}}(p) = 1` if `p^{-m} = q^{-m}`, and `0` otherwise. -/
def nu (m : ι) (q : ∀ k : {k : ι // k ≠ m}, E k) : Util E :=
  WithLp.toLp 2 (fun p : ∀ k, E k => if ∀ k (hk : k ≠ m), p k = q ⟨k, hk⟩ then (1 : ℝ) else 0)

/-- **Definition 4.1** (normalized games): `∑_{p^m ∈ E^m} u^m(p^m, p^{-m}) = 0` for all
`p^{-m}` and all `m`. Here `(p^m, p^{-m})` with `p^m = a` is `Function.update p m a`; the
`m`-th coordinate of `p` is irrelevant. -/
def IsNormalized (u : Games E) : Prop :=
  ∀ m (p : ∀ k, E k), ∑ a : E m, u m (Function.update p m a) = 0

/-- The **potential subspace** `P = {u ∈ C0^M | u = Π u and D u ∈ im δ0}` of (28). -/
def potentialSubspace : Submodule ℝ (Games E) :=
  LinearMap.eqLocus LinearMap.id (PiOp E) ⊓
    (LinearMap.range (delta0 (gameGraph E))).comap (Dop E)

/-- The **harmonic subspace** `H = {u ∈ C0^M | u = Π u and D u ∈ ker δ0*}` of (28). -/
def harmonicSubspace : Submodule ℝ (Games E) :=
  LinearMap.eqLocus LinearMap.id (PiOp E) ⊓
    (LinearMap.ker (LinearMap.adjoint (delta0 (gameGraph E)))).comap (Dop E)

/-- The **nonstrategic subspace** `N = {u ∈ C0^M | u ∈ ker D}` of (28). -/
def nonstrategicSubspace : Submodule ℝ (Games E) := LinearMap.ker (Dop E)

/-- The **potential component** `u_P = D† δ0 δ0† D u` of Theorem 4.1 (pseudoinverses for the
inner products (7) and the unweighted sum inner product on `C0^M`). -/
def potentialComponent : Games E →ₗ[ℝ] Games E :=
  pinv (Dop E) ∘ₗ delta0 (gameGraph E) ∘ₗ pinv (delta0 (gameGraph E)) ∘ₗ Dop E

/-- The **harmonic component** `u_H = D† (I - δ0 δ0†) D u` of Theorem 4.1. -/
def harmonicComponent : Games E →ₗ[ℝ] Games E :=
  pinv (Dop E) ∘ₗ (LinearMap.id - delta0 (gameGraph E) ∘ₗ pinv (delta0 (gameGraph E))) ∘ₗ Dop E

/-- The **nonstrategic component** `u_N = (I - D† D) u` of Theorem 4.1. -/
def nonstrategicComponent : Games E →ₗ[ℝ] Games E :=
  LinearMap.id - pinv (Dop E) ∘ₗ Dop E

/-- The function `φ = δ0† D u ∈ C0` of Theorem 4.1. -/
def potentialFunction : Games E →ₗ[ℝ] Util E := pinv (delta0 (gameGraph E)) ∘ₗ Dop E

end HarmonicGames.Decomposition

end


