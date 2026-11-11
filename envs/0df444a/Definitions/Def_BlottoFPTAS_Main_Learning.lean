-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Learning
-- name    : BlottoFPTAS_Main_Learning
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:01.374257+00:00
-- url     : https://prove2.me/theorems/24641a1c-b9b4-4f7a-98bf-b861a62d387a
-- title:
--   Codes, auxiliary marginals, the opponent payoff f, the weighted CDF distance d_v̂ and signed multipliers
-- statement:
--   Bids are identified with codes in a finite ordered set (the paper's $I=\{0,\dots,2^\Lambda-1\}$; here $\{0,\dots,N-1\}$). On $m$ battlefields with weights $w$: an **auxiliary marginal family** $p=(p_j)$ has a distribution $p_j$ on codes for each battlefield, with CDF $F_{p,j}(a)=\sum_{a'\le a}p_j(a')$; a code allocation $x$ has $F_{x,j}(a)=\mathbf 1\{x_j\le a\}$; a distribution $\pi$ on code allocations has marginals $\pi_j$ and $F_{\pi,j}(a)=\mathbb E_{x\sim\pi}F_{x,j}(a)$. The opponent's payoff is
--   $$f(p,q)=\sum_jw_j\sum_{a,a'}p_j(a)q_j(a')\Big(\mathbf 1\{a'>a\}+\tfrac12\mathbf 1\{a'=a\}\Big),$$
--   and the weighted CDF distance is $d_w(F,G)=\sum_jw_j\max_a|F_j(a)-G_j(a)|$. A **signed multiplier** $\lambda=(\lambda_j)$ has a distribution $\lambda_j$ on pairs $(s,a)\in\{-1,1\}\times I$, paired with a CDF family by $\lambda\cdot F=\sum_jw_j\sum_{s,a}\lambda_j(s,a)\,s\,F_j(a)$. `listDist` is the uniform distribution on a list of code allocations (counting repeats) and `avgAux` averages auxiliary families.
--
--   **Formalization Note.** The sign $s$ is a Boolean ($\mathrm{true}\mapsto1$, $\mathrm{false}\mapsto-1$).
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), pp. 36–37, §5.2

import Mathlib

open scoped BigOperators

namespace BlottoFPTAS.Main

/-!
# Codes, auxiliary marginals, the payoff `f`, the distance `d_v̂` and signed multipliers
(§5.2, pp. 35–39)

Bids are identified with integer codes in an ordered code set; the paper's code set is
`I = {0, …, 2^Λ − 1}`, here `Fin N` for a general `N`. On `m` battlefields with weights `w`:

* an **auxiliary marginal family** `p : Fin m → Fin N → ℝ` has a distribution `p_j` on codes for
  every battlefield (`IsAux`), with CDF `F_{p,j}(a) = ∑_{a′ ≤ a} p_j(a′)` (`cdfAux`);
* a **code allocation** `x : Fin m → Fin N` has CDF `F_{x,j}(a) = 1{x_j ≤ a}` (`cdfAlloc`);
* a **distribution `π` on code allocations** (`IsDist`: nonnegative weights summing to one on the
  finite type `Fin m → Fin N`) has marginals `π_j(a) = P_{x∼π}(x_j = a)` (`margOf`) and CDF
  `F_{π,j}(a) = E_{x∼π} F_{x,j}(a)`;
* the opponent's payoff `f(p, q) = ∑_j w_j ∑_{a,a′} p_j(a) q_j(a′)(1{a′ > a} + ½1{a′ = a})`
  (`fPay`), evaluated on marginals;
* the weighted CDF distance `d_w(F, G) = ∑_j w_j max_a |F_j(a) − G_j(a)|` (`dW`, on CDF
  families);
* a **signed multiplier** `λ : Fin m → Bool × Fin N → ℝ` has a distribution `λ_j` on pairs
  `(s, a)` for every battlefield (`IsMult`); the sign `s ∈ {−1, 1}` is encoded by `true ↦ 1`,
  `false ↦ −1` (`sgn`); its pairing with a CDF family is
  `λ · F = ∑_j w_j ∑_{(s,a)} λ_j(s, a) s F_j(a)` (`pair`);
* the uniform distribution on a list `x_1, …, x_T` of code allocations, counting repeats
  (`listDist`), and the average `T^{-1} ∑_t p_t` of auxiliary families (`avgAux`).
-/

/-- A family of distributions on codes, one per battlefield. -/
def IsAux {m N : ℕ} (p : Fin m → Fin N → ℝ) : Prop :=
  ∀ j, (∀ a, 0 ≤ p j a) ∧ ∑ a, p j a = 1

/-- A signed multiplier: a family of distributions on `{−1, 1} × codes`. -/
def IsMult {m N : ℕ} (l : Fin m → Bool × Fin N → ℝ) : Prop :=
  ∀ j, (∀ sa, 0 ≤ l j sa) ∧ ∑ sa, l j sa = 1

/-- A probability distribution on code allocations. -/
def IsDist {m N : ℕ} (π : (Fin m → Fin N) → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1

/-- The sign `s ∈ {−1, 1}` encoded by a Boolean. -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

/-- `F_{p,j}(a) = ∑_{a′ ≤ a} p_j(a′)`. -/
def cdfAux {m N : ℕ} (p : Fin m → Fin N → ℝ) (j : Fin m) (a : Fin N) : ℝ :=
  ∑ a' ∈ Finset.univ.filter (fun a' => a' ≤ a), p j a'

/-- `F_{x,j}(a) = 1{x_j ≤ a}`. -/
def cdfAlloc {m N : ℕ} (x : Fin m → Fin N) (j : Fin m) (a : Fin N) : ℝ :=
  if x j ≤ a then 1 else 0

/-- The marginals `π_j(a) = P_{x∼π}(x_j = a)` of a distribution on code allocations. -/
def margOf {m N : ℕ} (π : (Fin m → Fin N) → ℝ) (j : Fin m) (a : Fin N) : ℝ :=
  ∑ x, π x * if x j = a then 1 else 0

/-- `F_{π,j}(a) = E_{x∼π}[F_{x,j}(a)]`. -/
def cdfDistr {m N : ℕ} (π : (Fin m → Fin N) → ℝ) (j : Fin m) (a : Fin N) : ℝ :=
  ∑ x, π x * cdfAlloc x j a

/-- `f(p, q) = ∑_j w_j ∑_{a,a′} p_j(a) q_j(a′)(1{a′ > a} + ½ 1{a′ = a})`: the opponent's payoff
when the player's codes follow `p` and the opponent's follow `q`. -/
noncomputable def fPay {m N : ℕ} (w : Fin m → ℝ) (p q : Fin m → Fin N → ℝ) : ℝ :=
  ∑ j, w j * ∑ a, ∑ a', p j a * q j a' * (if a < a' then 1 else if a = a' then 1 / 2 else 0)

/-- `d_w(F, G) = ∑_j w_j max_a |F_j(a) − G_j(a)|` for CDF families `F`, `G`. -/
noncomputable def dW {m N : ℕ} (w : Fin m → ℝ) (F G : Fin m → Fin N → ℝ) : ℝ :=
  ∑ j, w j * ⨆ a : Fin N, |F j a - G j a|

/-- `λ · F = ∑_j w_j ∑_{(s,a)} λ_j(s, a) s F_j(a)`. -/
def pair {m N : ℕ} (w : Fin m → ℝ) (l : Fin m → Bool × Fin N → ℝ) (F : Fin m → Fin N → ℝ) : ℝ :=
  ∑ j, w j * ∑ sa : Bool × Fin N, l j sa * sgn sa.1 * F j sa.2

/-- The uniform distribution on the list `x_0, …, x_{T−1}`, counting repeats. -/
noncomputable def listDist {m N T : ℕ} (xs : Fin T → Fin m → Fin N) (x : Fin m → Fin N) : ℝ :=
  ((Finset.univ.filter fun t => xs t = x).card : ℝ) / T

/-- The average `T^{-1} ∑_t p_t` of auxiliary families. -/
noncomputable def avgAux {m N T : ℕ} (p : Fin T → Fin m → Fin N → ℝ) (j : Fin m) (a : Fin N) :
    ℝ :=
  (∑ t, p t j a) / T

end BlottoFPTAS.Main


