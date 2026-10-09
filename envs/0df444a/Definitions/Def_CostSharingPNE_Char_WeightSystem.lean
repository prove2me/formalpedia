-- Prove2me | Definitions.Def_CostSharingPNE_Char_WeightSystem
-- name    : CostSharingPNE_Char_WeightSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:58.139853+00:00
-- url     : https://prove2.me/theorems/bf7c34e5-6ff6-4043-9c56-d21a207f3612
-- title:
--   Tables 1–2 and (12)–(13) — weight systems, T̄, basis coefficients, the GWSV and GWMC rules, the GWSV basis rule (8) and the map h
-- statement:
--   A **weight system** $\omega=(\lambda,\Sigma)$ consists of strictly positive player weights $\lambda=(\lambda_1,\dots,\lambda_n)$ and an ordered partition $\Sigma=(S_1,\dots,S_K)$ of $N$ into priority blocks (blocks may be empty). For a nonempty coalition $T$ let $k=\min\{j: S_j\cap T\neq\emptyset\}$ and
--   $$
--   \overline T=T\cap S_k ,
--   $$
--   the members of $T$ in its highest-priority occupied block. For a welfare function $W$ the **basis coefficient** of $T$ is
--   $$
--   q^W_T=\sum_{R\subseteq T}(-1)^{|T|-|R|}\,W(R),
--   $$
--   the coefficient of the inclusion function $W^T$ in $W=\sum_T q^W_T W^T$.
--
--   The **generalized weighted Shapley value** rule is
--   $$
--   f^W_{GWSV}[\omega](i,S)=\sum_{T\subseteq S:\ i\in\overline T}\frac{\lambda_i}{\sum_{j\in\overline T}\lambda_j}\,q^W_T ,
--   $$
--   and the **generalized weighted marginal contribution** rule is $f^W_{GWMC}[\omega](i,S)=\lambda_i\bigl(W(\overline S_k)-W(\overline S_k-\{i\})\bigr)$ for $i\in S_k\cap S$, where $\overline S_k=S-\bigcup_{\ell<k}S_\ell$, and $0$ for $i\notin S$. The **GWSV basis rule** (8) on a coalition $T$ is
--   $$
--   f^T_{GWSV}[\omega](i,S)=\begin{cases}\lambda_i/\sum_{j\in\overline T}\lambda_j, & i\in\overline T\text{ and }T\subseteq S,\\ 0,&\text{otherwise.}\end{cases}
--   $$
--   Finally, the map $h$ of (12)–(13) sends $W'$ to the welfare function $W''$ with $W''(\emptyset)=0$ and $q^{W''}_T=q^{W'}_T/\sum_{j\in\overline T}\lambda_j$ for every nonempty $T$, that is $W''(S)=\sum_{\emptyset\ne T\subseteq S} q^{W'}_T/\sum_{j\in\overline T}\lambda_j$.
--
--   The GWSV rules are the rules that Theorem 1 shows to be the only ones guaranteeing equilibria; GWMC rules and $h$ give the equivalent form of Theorem 2.
--
--   **Formalization Note** A weight system stores the number of blocks `K`, the block index `block i : Fin K` of each player (0-based), and `lam` with `lam_pos`. This is exactly an ordered partition into possibly empty blocks. `tbar ω ∅ = ∅`, so a sum over `i ∈ T̄` never sees the empty coalition. `sbar ω S b` is $\overline S_k$ for the block `b` of player $i$.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Table 1 (p. 5), (2)–(3) (p. 7), Table 2 (8) (p. 8), Proposition 2 (12) and Theorem 2 (13) (p. 11)

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting

namespace CostSharingPNE.Char

/-- A weight system `ω = (λ, Σ)` (Table 1, p. 5): strictly positive player weights `λ` and an
ordered partition `Σ = (S_1, …, S_K)` of the players into `K` possibly empty blocks; player `i`
lies in the block with (0-based) index `block i`. -/
structure WeightSystem (n : ℕ) where
  K : ℕ
  block : Fin n → Fin K
  lam : Fin n → ℝ
  lam_pos : ∀ i, 0 < lam i

/-- `T̄ = T ∩ S_k` with `k = min {j : S_j ∩ T ≠ ∅}` (Table 1, p. 5): the players of a nonempty
coalition `T` in its first occupied block. Empty for `T = ∅`. -/
def tbar {n : ℕ} (ω : WeightSystem n) (T : Finset (Fin n)) : Finset (Fin n) :=
  if h : T.Nonempty then T.filter (fun i => ω.block i = T.inf' h ω.block) else ∅

/-- The basis (Möbius) coefficient `q^W_T = ∑_{R ⊆ T} (-1)^{|T| - |R|} W(R)` of `W` at `T`, the
inner sum of Table 1 and the coefficient of the inclusion function `W^T` in (3), p. 7. -/
def mobius {n : ℕ} (W : Welfare n) (T : Finset (Fin n)) : ℝ :=
  ∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card - R.card) * W R

/-- The generalized weighted Shapley value (Table 1, p. 5):
`f^W_GWSV[ω](i, S) = ∑_{T ⊆ S : i ∈ T̄} (λ_i / ∑_{j ∈ T̄} λ_j) q^W_T`. -/
noncomputable def gwsv {n : ℕ} (ω : WeightSystem n) (W : Welfare n) : Rule n :=
  fun i S => ∑ T ∈ S.powerset.filter (fun T => i ∈ tbar ω T),
    (ω.lam i / ∑ j ∈ tbar ω T, ω.lam j) * mobius W T

/-- `S̄_k = S − ⋃_{ℓ < k} S_ℓ`: the players of `S` in block `b` or a later block (Table 1). -/
def sbar {n : ℕ} (ω : WeightSystem n) (S : Finset (Fin n)) (b : Fin ω.K) : Finset (Fin n) :=
  S.filter (fun j => b ≤ ω.block j)

/-- The generalized weighted marginal contribution (Table 1, p. 5):
`f^W_GWMC[ω](i, S) = λ_i (W(S̄_k) − W(S̄_k − {i}))` with `i ∈ S_k`, and `0` for `i ∉ S`. -/
def gwmc {n : ℕ} (ω : WeightSystem n) (W : Welfare n) : Rule n :=
  fun i S => if i ∈ S then
    ω.lam i * (W (sbar ω S (ω.block i)) - W ((sbar ω S (ω.block i)).erase i))
  else 0

/-- The generalized weighted Shapley value basis rule (8) (Table 2, p. 8):
`f^T_GWSV[ω](i, S) = λ_i / ∑_{j ∈ T̄} λ_j` if `i ∈ T̄` and `T ⊆ S`, and `0` otherwise. -/
noncomputable def gwsvBasis {n : ℕ} (ω : WeightSystem n) (T : Finset (Fin n)) : Rule n :=
  fun i S => if i ∈ tbar ω T ∧ T ⊆ S then ω.lam i / ∑ j ∈ tbar ω T, ω.lam j else 0

/-- The map `h` of (12)–(13), p. 11: `h(W')` is the welfare function `W''` with `W''(∅) = 0` and
basis coefficients `q''_T = q'_T / ∑_{j ∈ T̄} λ_j` for every nonempty `T`, i.e.
`W''(S) = ∑_{∅ ≠ T ⊆ S} q'_T / ∑_{j ∈ T̄} λ_j`. -/
noncomputable def hmap {n : ℕ} (ω : WeightSystem n) (W' : Welfare n) : Welfare n :=
  fun S => ∑ T ∈ S.powerset.filter (fun T => T.Nonempty),
    mobius W' T / ∑ j ∈ tbar ω T, ω.lam j

end CostSharingPNE.Char


