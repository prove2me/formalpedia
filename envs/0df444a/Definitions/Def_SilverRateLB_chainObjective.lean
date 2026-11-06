-- Prove2me | Definitions.Def_SilverRateLB_chainObjective
-- name    : SilverRateLB_chainObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:33.812867+00:00
-- url     : https://prove2.me/theorems/e92ac3e3-f502-4ea8-8b68-33b8f1841793
-- title:
--   The global hard function $F$ of (9)–(11)
-- statement:
--   Fix a schedule $H$, an admissible checkpoint set $T$ with $k$ checkpoints and data $b_i,s_i$ of (4), constants $a,c$, and local data $(f_i,\tau_i)$, $1\le i\le k$. Set
--   $$D_1:=1,\quad \ell_1:=0,\quad D_{i+1}:=D_i\frac{b_i-2}{c(a+s_i)},\quad \ell_{i+1}:=D_i\tau_i\qquad(1\le i\le k).$$
--   On $\mathbb R^{k+1}$ define
--   $$\Phi_i(x):=D_i^2 f_i\Bigl(\frac{x^{(i)}-\ell_i}{D_i},\frac{x^{(i+1)}}{D_i}\Bigr)\ (1\le i\le k),\qquad \Phi_{k+1}(x):=H_\delta\bigl(x^{(k+1)}-\ell_{k+1}\bigr),\ \ \delta=\frac{D_{k+1}}{1+s_{k+1}},$$
--   and the **global hard function**
--   $$F(x):=\frac12\sum_{i=1}^k\Phi_i(x)+\frac12\Phi_{k+1}(x).$$
--   Each component couples two adjacent coordinates; the chain is the hard instance for the checkpoint set $T$ in Lemma 2.4.
--
--   **Formalization Note** Coordinates are 1-based. The local data are arguments; the theorems about $F$ assume that $(f_i,\tau_i)$ is a local hard function for gap $i$.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §3.1, (9), (10), (11), p. 12

import Mathlib
import Definitions.Def_SilverRateLB_gapMass
import Definitions.Def_SilverRateLB_oneSidedHuber

namespace SilverRateLB

/-- The excesses `D_i` of (9): `D_1 := 1`, `D_{i+1} := D_i (b_i − 2)/(c(a + s_i))`. -/
noncomputable def chainD (a c : ℝ) (H : List ℝ) (T : Finset ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (i + 2) => chainD a c H T (i + 1) *
      ((ckptStep H T (i + 1) - 2) / (c * (a + gapMass H T (i + 1))))

/-- The thresholds `ℓ_i` of (9): `ℓ_1 := 0`, `ℓ_{i+1} := D_i τ_i`. -/
noncomputable def chainEll (a c : ℝ) (H : List ℝ) (T : Finset ℕ) (τ : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i ≤ 1 then 0 else chainD a c H T (i - 1) * τ (i - 1)

/-- The 1-based coordinate `x^{(i)}` of `x ∈ ℝ^d` (`0` outside `1 ≤ i ≤ d`). -/
def coord {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i - 1 < d then x ⟨i - 1, h.2⟩ else 0

/-- **The global hard function** (9)–(11) of the proof of Lemma 2.4, in dimension `k + 1`:
`F(x) := ½ ∑_{i=1}^k Φ_i(x) + ½ Φ_{k+1}(x)` with
`Φ_i(x) := D_i² f_i((x^{(i)} − ℓ_i)/D_i, x^{(i+1)}/D_i)` and
`Φ_{k+1}(x) := H_δ(x^{(k+1)} − ℓ_{k+1})`, `δ = D_{k+1}/(1 + s_{k+1})`, built from local data
`(f_i, τ_i)`, `1 ≤ i ≤ k`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §3.1, (9),
(10), (11), p. 12: "Set D1 := 1, ℓ1 := 0, Di+1 := Di (bi−2)/(c(a+si)), ℓi+1 := Diτi (1 ≤ i ≤ k).
… Φi(x) := D_i² fi((x(i)−ℓi)/Di, x(i+1)/Di). … Set δ = Dk+1/(1+sk+1) and define the final
component by Φk+1(x) := Hδ(x(k+1) − ℓk+1). The full objective is F(x) := ½∑_{i=1}^k Φi(x) +
½Φk+1(x)."

**Formalization Note** `k = T.card`; the dimension `k + 1` is `Fin (T.card + 1)` with 1-based
coordinates via `coord`. The local data `f i`, `τ i` are arguments (used for `1 ≤ i ≤ k`); the
theorems assume they satisfy Lemma 3.2 (`IsLocalHard`) for gap `i`. -/
noncomputable def chainObjective (a c : ℝ) (H : List ℝ) (T : Finset ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ) (τ : ℕ → ℝ) :
    EuclideanSpace ℝ (Fin (T.card + 1)) → ℝ := fun x =>
  (1 / 2) * ∑ i ∈ Finset.Icc 1 T.card, chainD a c H T i ^ 2 *
      f i !₂[(coord x i - chainEll a c H T τ i) / chainD a c H T i,
        coord x (i + 1) / chainD a c H T i] +
    (1 / 2) * oneSidedHuber (chainD a c H T (T.card + 1) / (1 + gapMass H T (T.card + 1)))
      (coord x (T.card + 1) - chainEll a c H T τ (T.card + 1))

end SilverRateLB


