-- Prove2me | Definitions.Def_PNormReg_SMD
-- name    : PNormReg_SMD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:27.690277+00:00
-- url     : https://prove2.me/theorems/b54ca60a-bf89-4292-9e69-31b477912dda
-- title:
--   Algorithm 6: stochastic mirror descent for $\ell_2$-$\ell_q$ matrix games
-- statement:
--   For $M\in\mathbb R^{n\times d}$, $c\in\mathbb R^n$, $q\in(1,2]$ and $p=q/(q-1)$, the game is $\min_{\|x\|_2\le1}\max_{\|y\|_q\le1}y^\top Mx-c^\top y$. After normalizing $M$ and $c$ by $\Lambda$, Algorithm 6 sets $\tau_i=\|M_{i:}\|_2+|c_i|$, $\eta=\epsilon/(27\Lambda)$ and $T=\lceil162\Lambda^2/((q-1)\epsilon^2)\rceil$, and starts from $x^{(0)}=0$, $y^{(0)}=0$. Each round samples:
--
--   1. a row $i$ with probability $\|M_{i:}\|_2|y_i|/S$, where $S=\sum_i\|M_{i:}\|_2|y_i|$, if $S>0$, setting $\tilde u=S\,\mathrm{sign}(y_i)M_{i:}^\top/\|M_{i:}\|_2$ (and $\tilde u=0$ otherwise);
--   2. a column $j$ with probability $x_j^2/\|x\|_2^2$ if $x\ne0$, setting $\tilde v=c-\|x\|_2^2M_{:j}/x_j$ (and $\tilde v=c$ otherwise).
--
--   It then clips $\bar v_i=\mathrm{sign}(\tilde v_i)\min\{\eta|\tilde v_i|,\tau_i\}$, projects $x\leftarrow(x-\eta\tilde u)/\max\{1,\|x-\eta\tilde u\|_2\}$, and updates $w_i=\mathrm{sign}(y_i)|y_i|^{q-1}-(q-1)\bar v_i$ and $y_i\leftarrow\mathrm{sign}(w_i)(|w_i|/\max\{1,\|w\|_p\})^{p-1}$. The output is the average of the iterates $t=0,\dots,T$.
--
--   This module also defines the local-norm data of Lemma 19:
--
--   $$r(x,y)=\tfrac12\|x\|_2^2+\frac{\|y\|_q^q}{q(q-1)},\quad\|(u,v)\|^2_{(x,y)}=\|u\|_2^2+\sum_i\Big(\tau_i^{p-2}+\frac{|y_i|}{\tau_i}\Big)v_i^2,\quad\mathrm{clip}(u,v)=(u,(\mathrm{sign}(v_i)\min\{|v_i|,\tau_i\})_i),$$
--
--   and the duality gap $\max_{\|y\|_q\le1}h(x,y)-\min_{\|x'\|_2\le1}h(x',y)$.
--
--   **Formalization Note** A round's randomness is an element of `Option (Fin n) × Option (Fin d)`, with `none` meaning the line does not sample. The two samples are independent; the page gives each sample's marginal and the analysis uses only the marginals. The expectation is a finite recursive sum over the algorithm's own samples, with the averaged function inside it.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Algorithm 6, p.34; (49)–(51), p.37; (41), p.33

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_PNormReg_Scaled
import Definitions.Def_PNormReg_LocalNorm

open Matrix

namespace PNormReg

/-!
# Algorithm 6: stochastic mirror descent for `ℓ₂`-`ℓ_q` matrix games

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), Algorithm 6, p.34; (49)–(51), p.37; saddle operator,
p.34.

**Formalization Note.**
* A round's randomness is a pair `(o₁, o₂) : Option (Fin n) × Option (Fin d)`. `none` means the line
  does not sample: `S = 0` (line 8) or `x = 0` (line 11). The two samples are independent. Lines 9 and 12
  give each sample's marginal and the page does not couple them; the analysis only uses the marginals.
* `smdExpect` is the expectation over the algorithm's own samples, a finite sum. The function it
  averages sits inside the sum, so a duality gap's best responses are inside the expectation.
* `sign` is `Real.sign`, so `sign 0 = 0`; with `q > 1`, `|0|^{q−1} = 0` as on line 16.
* `p` is `conjExp q` throughout this section (§5: `p := q/(q − 1)`).
* `SMDState` keeps the running sums `∑_{t≤T} (x⁽ᵗ⁾, y⁽ᵗ⁾)` that line 18 averages.
-/

variable {n d : ℕ}

/-- The local-norm data of Lemma 19, (49)–(51), on `Z = B^d_2 × B^n_q`, with thresholds `τ`:
`r(x, y) = ½∥x∥₂² + ∥y∥_q^q/(q(q−1))`, `∇r(x, y) = (x, sign(y_i)|y_i|^{q−1}/(q−1))`,
`Ξ = ½ + 1/(q(q−1))`, `∥(u, v)∥²_(x,y) = ∥u∥₂² + ∑_i (τ_i^{p−2} + |y_i|/τ_i)v_i²` and
`clip(u, v) = (u, (sign(v_i) min{|v_i|, τ_i})_i)`. -/
noncomputable def l2lqSetup (q : ℝ) (τ : Fin n → ℝ) : LocalNormData d n where
  X := {x | l2Norm x ≤ 1}
  Y := {y | lpNorm q y ≤ 1}
  localNorm z γ := Real.sqrt (∑ j, γ.1 j ^ 2 +
    ∑ i, (τ i ^ (conjExp q - 2) + |z.2 i| / τ i) * γ.2 i ^ 2)
  r z := (1 / 2) * ∑ j, z.1 j ^ 2 + lpPow q z.2 / (q * (q - 1))
  gradR z := (z.1, fun i => Real.sign (z.2 i) * |z.2 i| ^ (q - 1) / (q - 1))
  Xi := 1 / 2 + 1 / (q * (q - 1))
  clip γ := (γ.1, fun i => Real.sign (γ.2 i) * min |γ.2 i| (τ i))

/-- The thresholds `τ_i := ∥M_{i:}∥₂ + |c_i|` of line 2. -/
noncomputable def tauOf (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) : Fin n → ℝ :=
  fun i => l2Norm (M i) + |c i|

/-- The saddle operator `g(x, y) = (M⊤y, c − Mx)` (p.34). -/
def saddleOp (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) (z : Pair d n) : Pair d n :=
  (Mᵀ *ᵥ z.2, c - M *ᵥ z.1)

/-- `S := ∑_i ∥M_{i:}∥₂|y_i|` of line 6. -/
noncomputable def rowSum (M : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, l2Norm (M i) * |y i|

/-- The law of line 9: `i` with probability `∥M_{i:}∥₂|y_i|/S` if `S > 0`, and no sample otherwise. -/
noncomputable def rowWeight (M : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) :
    Option (Fin n) → ℝ
  | none => if 0 < rowSum M y then 0 else 1
  | some i => if 0 < rowSum M y then l2Norm (M i) * |y i| / rowSum M y else 0

/-- The law of line 12: `j` with probability `x_j²/∥x∥₂²` if `x ≠ 0`, and no sample otherwise. -/
noncomputable def colWeight (x : Fin d → ℝ) : Option (Fin d) → ℝ
  | none => if x ≠ 0 then 0 else 1
  | some j => if x ≠ 0 then x j ^ 2 / l2Norm x ^ 2 else 0

/-- The row estimator: `ũ = 0` with no sample (line 7), and otherwise
`ũ = S sign(y_i)M⊤_{i:}/∥M_{i:}∥₂` (line 10). -/
noncomputable def rowEst (M : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) :
    Option (Fin n) → Fin d → ℝ
  | none => 0
  | some i => (rowSum M y * Real.sign (y i) / l2Norm (M i)) • M i

/-- The column estimator: `ṽ = c` with no sample (line 7), and otherwise
`ṽ = c − ∥x∥₂²M_{:j}/x_j` (line 13). -/
noncomputable def colEst (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) (x : Fin d → ℝ) :
    Option (Fin d) → Fin n → ℝ
  | none => c
  | some j => c - (l2Norm x ^ 2 / x j) • (fun i => M i j)

/-- The joint law of a round's two independent samples at `z = (x, y)`. -/
noncomputable def estWeight (M : Matrix (Fin n) (Fin d) ℝ) (z : Pair d n)
    (o : Option (Fin n) × Option (Fin d)) : ℝ :=
  rowWeight M z.2 o.1 * colWeight z.1 o.2

/-- The estimator `g̃(x, y) = (ũ, ṽ)` of Lemma 20 at outcome `o`. -/
noncomputable def estValue (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) (z : Pair d n)
    (o : Option (Fin n) × Option (Fin d)) : Pair d n :=
  (rowEst M z.2 o.1, colEst M c z.1 o.2)

/-- The iterate and the running sums of line 18. -/
structure SMDState (n d : ℕ) where
  x : Fin d → ℝ
  y : Fin n → ℝ
  sumX : Fin d → ℝ
  sumY : Fin n → ℝ

/-- Line 4: `x⁽⁰⁾ = 0`, `y⁽⁰⁾ = 0`, and the running sums start at `(x⁽⁰⁾, y⁽⁰⁾) = 0`. -/
def smdInit : SMDState n d := ⟨0, 0, 0, 0⟩

/-- Lines 14–17 of one round at outcome `o`, with `M`, `c` the normalized values. -/
noncomputable def smdStep (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) (q η : ℝ)
    (s : SMDState n d) (o : Option (Fin n) × Option (Fin d)) : SMDState n d :=
  let u := rowEst M s.y o.1
  let v := colEst M c s.x o.2
  let vbar : Fin n → ℝ := fun i => Real.sign (v i) * min (η * |v i|) (tauOf M c i)
  let x' : Fin d → ℝ := (1 / max 1 (l2Norm (s.x - η • u))) • (s.x - η • u)
  let w : Fin n → ℝ := fun i => Real.sign (s.y i) * |s.y i| ^ (q - 1) - (q - 1) * vbar i
  let y' : Fin n → ℝ := fun i =>
    Real.sign (w i) * (|w i| / max 1 (lpNorm (conjExp q) w)) ^ (conjExp q - 1)
  ⟨x', y', s.sumX + x', s.sumY + y'⟩

/-- The expectation of `φ` of the state after `t` more rounds, from `s`. -/
noncomputable def smdExpect (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) (q η : ℝ) :
    ℕ → (SMDState n d → ℝ) → SMDState n d → ℝ
  | 0, φ, s => φ s
  | t + 1, φ, s => ∑ o, estWeight M (s.x, s.y) o * smdExpect M c q η t φ (smdStep M c q η s o)

/-- Line 3: `T = ⌈162Λ²/((q−1)ϵ²)⌉`. -/
noncomputable def smdT (q ε Λ : ℝ) : ℕ := ⌈162 * Λ ^ 2 / ((q - 1) * ε ^ 2)⌉₊

/-- Line 18: `(x̄, ȳ) = (1/(T+1))∑_{t=0}^T (x⁽ᵗ⁾, y⁽ᵗ⁾)`. -/
noncomputable def smdAverage (T : ℕ) (s : SMDState n d) : Pair d n :=
  (((T : ℝ) + 1)⁻¹ • s.sumX, ((T : ℝ) + 1)⁻¹ • s.sumY)

/-- The duality gap `max_{y∈B^n_q} h(x, y) − min_{x′∈B^d_2} h(x′, y)` of the game (40) at `z = (x, y)`.
Both balls contain `0` and `h` is continuous, so the real `sSup` and `sInf` are the max and min. -/
noncomputable def dualityGap (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) (q : ℝ) (z : Pair d n) :
    ℝ :=
  sSup ((fun y => gameObj M c z.1 y) '' {y | lpNorm q y ≤ 1}) -
    sInf ((fun x => gameObj M c x z.2) '' {x | l2Norm x ≤ 1})

end PNormReg


