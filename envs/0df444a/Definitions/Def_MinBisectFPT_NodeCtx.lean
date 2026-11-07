-- Prove2me | Definitions.Def_MinBisectFPT_NodeCtx
-- name    : MinBisectFPT_NodeCtx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:16.167294+00:00
-- url     : https://prove2.me/theorems/4df39cc5-635b-4ad9-98ff-2875ac7b2427
-- title:
--   Standing assumptions of §4, tables $C_t$, partition function $F(W)$, Möbius terms $\Psi(U)$
-- statement:
--   Throughout §§4.1–4.3, $G$ is connected, $k\ge1$, $(T,\beta)$ is a rooted tree decomposition of $G$ with (D1)–(D3), and $q=3k$. Fix a node $t$, with $\beta=\beta(t)$, $\sigma=\sigma(t)$, $H=G_t$, $B=B_t$. Cut sizes are taken in $H$.
--
--   1. The **table** is $C_t(T,\ell,j)=|\{X\subseteq\gamma(t):X\cap\sigma(t)=T,\ |X\cap\alpha(t)|=\ell,\ |\delta_{G_t}(X)|=j\}|$.
--   2. The **bag partition function** of $W\subseteq\beta$ is
--   $$F(W)=\sum_{X\subseteq\gamma(t):\,X\cap\beta\subseteq W}x^{|X\cap\beta|}y^{|X\cap\alpha(t)|}z^{|\delta(X)|}u^{X\cap\sigma}.$$
--   3. The **row** of a child $c$ for the pattern $T$ is $P_c(T)=\sum_{\ell,j}C_c(T,\ell,j)y^\ell z^j$, over $\ell\le|\alpha(c)|$, $j\le k$.
--   4. The **Möbius term** of $U\subseteq\beta$ is $\Psi(U)=\sum_{W\subseteq U}(-1)^{|U\setminus W|}\log F(W)$, with $\log F(W)$ the finite series with $N=q+k$.
--   5. A configuration $X\subseteq\gamma(t)$ is **small** if $|X\cap\beta|\le q$, and $C^{\mathrm{sm}}_t(T,\ell,j)$ counts small configurations with pattern $T$, size $\ell$ and cut $j$.
--
--   **Formalization Note** The standing assumptions are bundled in a structure, so nothing in §4 can be stated for a graph that fails them. Lemma 4.2 uses other truncations $x^{q'+1}$, so $F$ carries $q'$ as a parameter.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), §4, p.10; §4.1, pp.11–12; §4.2, p.12

import Mathlib
import Definitions.Def_MinBisectFPT_IsUnbreakableTD
import Definitions.Def_MinBisectFPT_TruncRing
import Definitions.Def_MinBisectFPT_expN

open scoped Classical

namespace MinBisectFPT

/-- **The table `C_t`.** Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*, STOC
2027 submission (manuscript sha256 8db80a52…), §4.1, p.11:
`C_t(T, ℓ, j) = |{X ⊆ γ(t) : X ∩ σ(t) = T, |X ∩ α(t)| = ℓ, |δ_{G_t}(X)| = j}|`. -/
noncomputable def tableCount {n : ℕ} (G : SimpleGraph (Fin n)) (D : RootedTD n) (t : Fin D.N)
    (T : Finset (Fin n)) (l j : ℕ) : ℕ :=
  ((D.cone t).powerset.filter fun X =>
    X ∩ D.adhesion t = T ∧ (X ∩ D.component t).card = l ∧ cutSize (subtreeGraph G D t) X = j).card

/-- **The standing assumptions of §§4.1–4.3** (p.10), with the fixed node of §4.1: "the graph G is
connected, k ≥ 1, and (T, β) is a rooted tree decomposition of G with properties (D1)–(D3) of
Theorem 1.3", and `t` a node. -/
structure NodeCtx (n : ℕ) where
  G : SimpleGraph (Fin n)
  k : ℕ
  D : RootedTD n
  t : Fin D.N
  connected : G.Connected
  one_le_k : 1 ≤ k
  isRootedTD : IsRootedTD G D
  unbreakable : IsUnbreakableTD G D k

namespace NodeCtx

variable {n : ℕ} (ctx : NodeCtx n)

/-- `q = 3k` (p.10). -/
def q : ℕ := 3 * ctx.k
/-- `β = β(t)`. -/
abbrev β : Finset (Fin n) := ctx.D.bag ctx.t
/-- `σ = σ(t)`. -/
abbrev σ : Finset (Fin n) := ctx.D.adhesion ctx.t
/-- `α(t)`. -/
noncomputable abbrev α : Finset (Fin n) := ctx.D.component ctx.t
/-- `γ(t)`. -/
noncomputable abbrev γ : Finset (Fin n) := ctx.D.cone ctx.t
/-- `H = G_t` (p.11). -/
noncomputable abbrev H : SimpleGraph (Fin n) := subtreeGraph ctx.G ctx.D ctx.t
/-- `B = B_t` (p.11). -/
noncomputable abbrev B : SimpleGraph (Fin n) := bagGraph ctx.G ctx.D ctx.t

/-- `R_t` with `x` truncated at `x^{q′+1}` (p.11; Lemma 4.2). -/
noncomputable abbrev Rt (q' : ℕ) : Type := TruncRing ctx.σ ctx.α.card ctx.k q'

/-- The monomial `x^i y^l z^j u^T` in `R_t` (p.11). -/
noncomputable def monoT (q' i l j : ℕ) (T : Finset (Fin n)) : ctx.Rt q' :=
  mono ctx.σ ctx.α.card ctx.k q' i l j T

/-- `J_t` (p.12). -/
noncomputable def J (q' : ℕ) : Ideal (ctx.Rt q') := idealJ ctx.σ ctx.α.card ctx.k q'

/-- **The bag partition function** (p.11):
`F(W) = Σ_{X⊆γ(t): X∩β⊆W} x^{|X∩β|} y^{|X∩α(t)|} z^{|δ(X)|} u^{X∩σ}`, cuts taken in `H = G_t`. -/
noncomputable def F (q' : ℕ) (W : Finset (Fin n)) : ctx.Rt q' :=
  ∑ X ∈ ctx.γ.powerset.filter (fun X => X ∩ ctx.β ⊆ W),
    ctx.monoT q' (X ∩ ctx.β).card (X ∩ ctx.α).card (cutSize ctx.H X) (X ∩ ctx.σ)

/-- **The row** `P_c(T) = Σ_{ℓ,j} C_c(T, ℓ, j) y^ℓ z^j` of the table of `c` for the pattern `T`, in
`R_t` (Lemma 4.2, p.11). The sum runs over the table's range `ℓ ≤ |α(c)|`, `j ≤ k`. -/
noncomputable def row (q' : ℕ) (c : Fin ctx.D.N) (T : Finset (Fin n)) : ctx.Rt q' :=
  ∑ l ∈ Finset.range ((ctx.D.component c).card + 1), ∑ j ∈ Finset.range (ctx.k + 1),
    ((tableCount ctx.G ctx.D c T l j : ℕ) : ctx.Rt q') * ctx.monoT q' 0 l j ∅

/-- `log F(W)`, the finite series `log(1 + f)` with `f = F(W) − 1` and `N = q + k` (§4.2, p.12). -/
noncomputable def logF (W : Finset (Fin n)) : ctx.Rt ctx.q :=
  logN (ctx.q + ctx.k) (ctx.F ctx.q W - 1)

/-- **The Möbius term** `Ψ(U) = Σ_{W⊆U} (−1)^{|U\W|} log F(W)` (§4.2, p.12). -/
noncomputable def Psi (U : Finset (Fin n)) : ctx.Rt ctx.q :=
  ∑ W ∈ U.powerset, ((-1 : ℤ) ^ (U \ W).card) • ctx.logF W

/-- The number of configurations with `|X ∩ β| = i`, pattern `T`, size `l` and cut `j` (p.12). Its sum
over `i ≤ q` is `C^sm_t(T, l, j)`; it is the coefficient of `x^i y^l z^j u^T` in `F(β)`. -/
noncomputable def bagCount (i : ℕ) (T : Finset (Fin n)) (l j : ℕ) : ℕ :=
  (ctx.γ.powerset.filter fun X =>
    (X ∩ ctx.β).card = i ∧ X ∩ ctx.σ = T ∧ (X ∩ ctx.α).card = l ∧ cutSize ctx.H X = j).card

/-- **`C^sm_t(T, l, j)`** (p.12): "the number of small configurations with pattern T, size ℓ and cut
j", where `X` is small if `|X ∩ β| ≤ q`. -/
noncomputable def smallCount (T : Finset (Fin n)) (l j : ℕ) : ℕ :=
  (ctx.γ.powerset.filter fun X =>
    (X ∩ ctx.β).card ≤ ctx.q ∧ X ∩ ctx.σ = T ∧ (X ∩ ctx.α).card = l ∧ cutSize ctx.H X = j).card

end NodeCtx

end MinBisectFPT


