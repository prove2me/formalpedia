-- Prove2me | Definitions.Def_RefugeeCash_PDCA_Model
-- name    : RefugeeCash_PDCA_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:23.711273+00:00
-- url     : https://prove2.me/theorems/c70acf8f-3e91-439e-b485-c15d5040b82d
-- title:
--   §4–§6, pp. 9–22 — HO cash/in-kind assistance, monopolist retailer, symmetric-goods profit, Assumption 2, the PDCA scheme (27) and its n-good form (22)–(24)
-- statement:
--   The model of Kotsi, Wu and Pedraza-Martinez, *Donations for Refugee Crises: In-kind Versus Cash Assistance*. A humanitarian organization (HO) has a budget $B$ for a refugee assistance program. It gives a fraction $k \in [0,1]$ of the budget to the refugees as cash and spends the rest on in-kind goods bought at wholesale unit cost $c$. A local monopolist retailer, which also buys at unit cost $c$, sets retail prices and sells both to the local residents and to the refugees.
--
--   **Symmetric goods** (§5). All goods have the same cost $c$ and price $p$, and $D(p)$ is the residents' aggregate demand. The refugees spend their cash $kB$ in full, so they buy $Q(p,k) = kB/p$ units. The retailer's profits are
--   $$\pi_r(p,k) = (p-c)\,Q(p,k), \qquad \pi_0(p) = (p-c)\,D(p), \qquad \Pi(p,k) = \pi_r(p,k) + \pi_0(p) \quad (18).$$
--   The standing assumptions are $B > 0$ and $c > 0$.
--
--   **Assumption 2.** There is $p_{\max} > c$ with $D(p_{\max}) = 0$; $D$ is continuously differentiable and $D'(p) \le 0$ for $p \in (c, p_{\max})$; and $\pi_0$ is unimodal with unique maximizer $p_0 > c$. The pre-arrival maximum profit is $\Pi_0 := \pi_0(p_0)$, equation (4).
--
--   **The symmetric PDCA scheme** (27). For a target price $p^\odot$ and target cash fraction $k^\odot$, the price-dependent cash assistance pays the fraction
--   $$k(p) = \min\Big\{\big(k^\odot + S(p^\odot,k^\odot)(p-p^\odot)\big)^+,\ 1\Big\}, \qquad S(p^\odot,k^\odot) = -\,\frac{\dfrac{k^\odot c}{(p^\odot)^2} + \dfrac{\pi_0'(p^\odot)}{B}}{1 - \dfrac{c}{p^\odot}},$$
--   and the retailer, anticipating it, earns $k(p)B(1-c/p) + \pi_0(p) = \Pi(p, k(p))$ at price $p$.
--
--   **$n$ goods** (§4, Proposition 4). Prices $\mathbf p$ and costs $\mathbf c$ are vectors in $\mathbb R^n$, $\mathbf Q(\mathbf p,k,\mathbf g)$ is the refugees' aggregate demand under cash fraction $k$ and in-kind assistance $\mathbf g$, and $\mathbf D(\mathbf p)$ the residents' demand. Then $\pi_r(\mathbf p,k,\mathbf g) = (\mathbf p-\mathbf c)^\top\mathbf Q(\mathbf p,k,\mathbf g)$, $\pi_0(\mathbf p) = (\mathbf p - \mathbf c)^\top \mathbf D(\mathbf p)$ and $\Pi = \pi_r + \pi_0$, equation (5). With the budget-balancing in-kind assistance $\mathbf g^\odot(1-k)/(1-k^\odot)$, the refugee profit is $\tilde\pi_r(\mathbf p,k) := \pi_r(\mathbf p, k, \mathbf g^\odot(1-k)/(1-k^\odot))$, equation (15). The PDCA policy of Proposition 4 uses the weights $v_i := \partial\Pi(\mathbf p^\odot,k^\odot,\mathbf g^\odot)/\partial p_i$ (22), the price index $p_{\mathbf v} = \mathbf p^\top \mathbf v$, and
--   $$k(p_{\mathbf v}) = \min\{(a + s\,p_{\mathbf v})^+, 1\},\quad s = -\Big(\frac{\partial\tilde\pi_r(\mathbf p^\odot,k^\odot)}{\partial k}\Big)^{-1},\quad a = k^\odot - s\,\mathbf p^{\odot\top}\mathbf v, \qquad \mathbf g(p_{\mathbf v}) = \frac{\mathbf g^\odot(1-k(p_{\mathbf v}))}{1-k^\odot},$$
--   equations (23)–(24). The retailer's PDCA objective is $\tilde\pi_r(\mathbf p, k(\mathbf p^\top\mathbf v)) + \pi_0(\mathbf p)$, the objective of (16).
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real numbers. The page gives no domain for "continuously differentiable" or "unimodal" in Assumption 2; both are read on the price range $(c,\infty)$, and "unimodal with the unique maximizer $p_0$" is read as: $\pi_0$ nondecreasing on $(c, p_0]$, nonincreasing on $[p_0, \infty)$, and $\pi_0(p) < \pi_0(p_0)$ for every other $p > c$. Reading continuous differentiability on $(c,\infty)$ excludes a demand truncated to $0$ at $p_{\max}$ (not differentiable there), so it is a stronger hypothesis than a reading on $(c, p_{\max})$ only. $\Pi_0$ is the value $\pi_0(p_0)$, not a supremum. The derivative $\pi_0'(p^\odot)$ is Lean's `deriv`, which is the true derivative wherever it is used ($p^\odot > c$, where Assumption 2 makes $D$, hence $\pi_0$, differentiable). Partial derivatives in the $n$-good model are Fréchet derivatives applied to the unit vectors, and $\mathbf Q$, $\mathbf D$ are abstract functions: Proposition 4 never uses the form of $\mathbf Q$ derived from the refugees' problem (1)–(2). The divisions in $Q$, $S$, $s$ and $\mathbf g(\cdot)$ are by $p$, $(p^\odot)^2$, $1-c/p^\odot$, $\partial\tilde\pi_r/\partial k$ and $1-k^\odot$; every theorem keeps these nonzero through its hypotheses.
-- source:
--   Kotsi, Wu & Pedraza-Martinez, Donations for Refugee Crises: In-kind Versus Cash Assistance, manuscript of November 27, 2021 (MSOM, DOI 10.1287/msom.2021.1073), pp. 9–22 (PDF 10–23): §4.1 p. 9, eq. (2) p. 10, eqs. (4)–(5) pp. 11–12, eq. (15) p. 15, §5 p. 16, Assumption 2 pp. 16–17, eq. (18) p. 17, Proposition 4 eqs. (22)–(24) pp. 19–20, §6.3 eq. (27) p. 22

import Mathlib

namespace RefugeeCash.PDCA

/-! ### Symmetric goods (§5, pp. 16–17; §6.3, pp. 20–22)

Kotsi, Wu & Pedraza-Martinez, *Donations for Refugee Crises: In-kind Versus Cash Assistance*,
manuscript of November 27, 2021. With symmetric goods every good has the same unit cost `c` and
the same price `p`, and `D p` is the local residents' aggregate demand for the `n` goods (p. 16). -/

/-- Data of the symmetric-goods model: total budget `B` of the HO's assistance program, unit
wholesale cost `c` paid by the retailer and by the HO, and the local residents' aggregate demand
function `D` (§4.1, p. 9; §5, p. 16). -/
structure Params where
  /-- total budget `B` -/
  B : ℝ
  /-- unit wholesale cost `c` -/
  c : ℝ
  /-- local residents' aggregate demand `D(p)` -/
  D : ℝ → ℝ

/-- Standing assumptions: a positive budget `B > 0` and a positive unit cost `c > 0`. -/
def Params.Standing (P : Params) : Prop := 0 < P.B ∧ 0 < P.c

/-- Refugees' purchases from the retailer under cash assistance `kB`: they spend the cash in full,
so `Q(p, k) = kB/p` (§5, p. 16). -/
noncomputable def refugeeDemand (P : Params) (p k : ℝ) : ℝ := k * P.B / p

/-- The retailer's profit from selling to the refugees, `πr(p, k) = (p − c) Q(p, k)`
(the first profit component of (5), p. 12, specialised to symmetric goods). -/
noncomputable def piR (P : Params) (p k : ℝ) : ℝ := (p - P.c) * refugeeDemand P p k

/-- The retailer's profit from the local residents, `π0(p) = (p − c) D(p)` (§4.3, p. 11; p. 17). -/
def pi0 (P : Params) (p : ℝ) : ℝ := (p - P.c) * P.D p

/-- The retailer's total profit after the refugees' arrival, `Π(p, k) = πr(p, k) + π0(p)`,
equation (18), p. 17. -/
noncomputable def retailerProfit (P : Params) (p k : ℝ) : ℝ := piR P p k + pi0 P p

/-- Assumption 2 (pp. 16–17), with its `p_max` and `p0` as arguments: `p_max > c` with
`D(p_max) = 0`; `D` is continuously differentiable (read on `(c, ∞)`); `D′(p) ≤ 0` on
`(c, p_max)`; and `π0` is unimodal on `(c, ∞)` with the unique maximizer `p0 > c`, read as:
nondecreasing on `(c, p0]`, nonincreasing on `[p0, ∞)`, and `π0(p) < π0(p0)` for every other
`p > c`. -/
def Assumption2 (P : Params) (pmax p0 : ℝ) : Prop :=
  P.c < pmax ∧ P.D pmax = 0 ∧ ContDiffOn ℝ 1 P.D (Set.Ioi P.c) ∧
    (∀ p ∈ Set.Ioo P.c pmax, deriv P.D p ≤ 0) ∧
    P.c < p0 ∧ MonotoneOn (pi0 P) (Set.Ioc P.c p0) ∧ AntitoneOn (pi0 P) (Set.Ici p0) ∧
    ∀ p ∈ Set.Ioi P.c, p ≠ p0 → pi0 P p < pi0 P p0

/-- The retailer's maximum profit before the refugees' arrival, `Π0 := π0(p0)`, equation (4),
p. 12, with `p0` the maximizer of Assumption 2. -/
def Pi0 (P : Params) (p0 : ℝ) : ℝ := pi0 P p0

/-- The slope coefficient of the symmetric PDCA scheme, equation (27), p. 22:
`S(p⊙, k⊙) = −(k⊙ c / p⊙² + π0′(p⊙)/B) / (1 − c/p⊙)`. -/
noncomputable def slope (P : Params) (pT kT : ℝ) : ℝ :=
  -((kT * P.c / pT ^ 2 + deriv (pi0 P) pT / P.B) / (1 - P.c / pT))

/-- The symmetric PDCA scheme, equation (27), p. 22:
`k(p) = min{(k⊙ + S(p⊙, k⊙)(p − p⊙))⁺, 1}`. -/
noncomputable def kPDCA (P : Params) (pT kT p : ℝ) : ℝ :=
  min (max (kT + slope P pT kT * (p - pT)) 0) 1

/-- The retailer's profit at price `p` under the symmetric PDCA scheme,
`k(p) B (1 − c/p) + π0(p)` (§6.3, p. 22), i.e. `Π(p, k(p))`. -/
noncomputable def pdcaProfit (P : Params) (pT kT p : ℝ) : ℝ :=
  retailerProfit P p (kPDCA P pT kT p)

/-! ### `n` goods (§4, pp. 9–15; §6.2, Proposition 4, pp. 19–20) -/

/-- Data of the `n`-good model: budget `B`, unit costs `c`, the refugees' aggregate demand
`Q(p, k, g)` for prices `p`, cash fraction `k` and in-kind assistance `g` (equation (2), p. 10),
and the local residents' demand `D(p)` (§4.3, p. 11). -/
structure GenParams (n : ℕ) where
  /-- total budget `B` -/
  B : ℝ
  /-- unit costs `c = (c₁, …, cₙ)` -/
  c : Fin n → ℝ
  /-- refugees' aggregate demand `Q(p, k, g)` -/
  Q : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  /-- local residents' demand `D(p)` -/
  D : (Fin n → ℝ) → (Fin n → ℝ)

namespace GenParams

variable {n : ℕ} (M : GenParams n)

/-- `πr(p, k, g) := (p − c)ᵀ Q(p, k, g)`, p. 12. -/
def piR (p : Fin n → ℝ) (k : ℝ) (g : Fin n → ℝ) : ℝ := (p - M.c) ⬝ᵥ M.Q p k g

/-- `π0(p) = (p − c)ᵀ D(p)`, p. 11. -/
def pi0 (p : Fin n → ℝ) : ℝ := (p - M.c) ⬝ᵥ M.D p

/-- `Π(p, k, g) := πr(p, k, g) + π0(p)`, equation (5), p. 12. -/
def profit (p : Fin n → ℝ) (k : ℝ) (g : Fin n → ℝ) : ℝ := M.piR p k g + M.pi0 p

/-- `π̃r(p, k) := πr(p, k, g⊙(1 − k)/(1 − k⊙))`, equation (15), p. 15. -/
noncomputable def piRtilde (kT : ℝ) (gT : Fin n → ℝ) (p : Fin n → ℝ) (k : ℝ) : ℝ :=
  M.piR p k (((1 - k) / (1 - kT)) • gT)

/-- The PDCA weights `v_i := ∂Π(p⊙, k⊙, g⊙)/∂p_i`, equation (22), p. 19. -/
noncomputable def vPDCA (pT : Fin n → ℝ) (kT : ℝ) (gT : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ (fun p => M.profit p kT gT) pT (Pi.single i 1)

/-- `s = −(∂π̃r(p⊙, k⊙)/∂k)⁻¹`, equation (23), p. 20. -/
noncomputable def sPDCA (pT : Fin n → ℝ) (kT : ℝ) (gT : Fin n → ℝ) : ℝ :=
  -(deriv (fun k => M.piRtilde kT gT pT k) kT)⁻¹

/-- `a = k⊙ − s p⊙ᵀ v`, equation (23), p. 20. -/
noncomputable def aPDCA (pT : Fin n → ℝ) (kT : ℝ) (gT : Fin n → ℝ) : ℝ :=
  kT - M.sPDCA pT kT gT * (pT ⬝ᵥ M.vPDCA pT kT gT)

/-- The cash fraction as a function of the price index `x = pᵀv`:
`k(x) = min{(a + s x)⁺, 1}`, equation (23), p. 20. -/
noncomputable def kOf (pT : Fin n → ℝ) (kT : ℝ) (gT : Fin n → ℝ) (x : ℝ) : ℝ :=
  min (max (M.aPDCA pT kT gT + M.sPDCA pT kT gT * x) 0) 1

/-- The in-kind assistance as a function of the price index:
`g(x) = g⊙(1 − k(x))/(1 − k⊙)`, equation (24), p. 20. -/
noncomputable def gOf (pT : Fin n → ℝ) (kT : ℝ) (gT : Fin n → ℝ) (x : ℝ) : Fin n → ℝ :=
  ((1 - M.kOf pT kT gT x) / (1 - kT)) • gT

/-- The retailer's objective under the PDCA policy, `π̃r(p, k(pᵀv)) + π0(p)`, the objective of
(16), p. 15. -/
noncomputable def pdcaProfitGen (pT : Fin n → ℝ) (kT : ℝ) (gT : Fin n → ℝ)
    (p : Fin n → ℝ) : ℝ :=
  M.piRtilde kT gT p (M.kOf pT kT gT (p ⬝ᵥ M.vPDCA pT kT gT)) + M.pi0 p

end GenParams

end RefugeeCash.PDCA


