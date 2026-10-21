-- Prove2me | Definitions.Def_BellDetEff_TwoParty_BellInequality
-- name    : BellDetEff_TwoParty_BellInequality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:02.03099+00:00
-- url     : https://prove2.me/theorems/278adda2-f0bf-49e7-a156-46e55f1a356f
-- title:
--   The mod-P Bell expression I_{M_A M_B (P+1)(P+1)} (6) and the no-signaling witness box (13) (pp. 2–3)
-- statement:
--   This file defines the Bell inequality built in the proof of Theorem 2 of Cao and Peng, and the no-signaling behaviour that violates it.
--
--   Fix a natural number $P$ (a prime in all results). Each party has the $P$ ordinary outputs $0,1,\dots,P-1$ and the empty output $\Phi$. Inputs are $x\in\{1,\dots,M_A\}$, $y\in\{1,\dots,M_B\}$, and congruences are modulo $P$.
--
--   1. **Coefficients (eq. (6)).**
--   $$f(a,b,x,y)=\begin{cases}1 & (x>1\ \vee\ y>1)\ \wedge\ a+b\equiv xy,\\ 0 & x=1\ \wedge\ y=1\ \wedge\ a+b\equiv xy,\\ -P^4 & \text{otherwise,}\end{cases}\qquad g(a,x)=\begin{cases}-1 & x>1\\ 0 & x=1\end{cases},\qquad h(b,y)=\begin{cases}-1 & y>1\\ 0 & y=1\end{cases}.$$
--   2. **Bell expression (eq. (6)).** For a behaviour $p$ with outputs in $\{0,\dots,P-1\}\cup\{\Phi\}$,
--   $$I_{M_AM_B(P+1)(P+1)}(p)=\sum_{a,b,x,y} f(a,b,x,y)\,p(a,b\mid x,y)+\sum_{a,x} g(a,x)\,p(a\mid x)+\sum_{b,y}h(b,y)\,p(b\mid y),$$
--   where $a,b$ range over $\{0,\dots,P-1\}$ only (the empty output carries coefficient $0$) and $p(a\mid x)$, $p(b\mid y)$ are the one-party marginals (averaged over the other party's input).
--   3. **Witness box (eq. (13)).** $p^{NS}(a,b\mid x,y)=1/P$ if $a+b\equiv xy \pmod P$ and $0$ otherwise, for $a,b\in\{0,\dots,P-1\}$.
--
--   The proof of Theorem 2 shows that $I\le 0$ for every local hidden variable model, while the witness box under efficiency $\eta$ attains $I=\eta^2(M_AM_B-1)-\eta(M_A+M_B-2)$.
--
--   **Formalization Note** Outputs are `Fin P`, read in `ZMod P` through their values; the empty output is `none` in `Option (Fin P)`. The paper's inputs are `x.val + 1`, `y.val + 1`, so the congruence is $a+b\equiv (x.\mathrm{val}+1)(y.\mathrm{val}+1)$ and the test $x>1$ is `x.val ≠ 0`. The paper takes $P$ to be the minimal prime with $P\ge\max(M_A,M_B)$; the definitions take any $P$, and the results are stated for every prime $P\ge\max(M_A,M_B)$, which is stronger since minimality is never used.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, p. 2, proof of Theorem 2, eq. (6); p. 3, eq. (13)

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_Behaviour

namespace BellDetEff.TwoParty

/-- The congruence `a + b ≡ x y (mod P)` of eq. (6), p. 2, for outputs `a, b ∈ {0, …, P − 1}`
and the paper's 1-based inputs `x.val + 1`, `y.val + 1`. -/
def bellCong (P : ℕ) {MA MB : ℕ} (a b : Fin P) (x : Fin MA) (y : Fin MB) : Prop :=
  ((a.val : ZMod P) + (b.val : ZMod P)) = ((x.val + 1 : ℕ) : ZMod P) * ((y.val + 1 : ℕ) : ZMod P)

instance (P : ℕ) {MA MB : ℕ} (a b : Fin P) (x : Fin MA) (y : Fin MB) :
    Decidable (bellCong P a b x y) := by
  unfold bellCong; infer_instance

/-- The coefficient `f(a, b, x, y)` of eq. (6): `1` if `(x > 1 ∨ y > 1)` and `a + b ≡ xy`,
`0` if `x = y = 1` and `a + b ≡ xy`, and `−P⁴` otherwise (paper's 1-based inputs; `x > 1` is
`x.val ≠ 0`). -/
noncomputable def bellF (P : ℕ) {MA MB : ℕ} (a b : Fin P) (x : Fin MA) (y : Fin MB) : ℝ :=
  if (x.val ≠ 0 ∨ y.val ≠ 0) ∧ bellCong P a b x y then 1
  else if x.val = 0 ∧ y.val = 0 ∧ bellCong P a b x y then 0
  else -((P : ℝ) ^ 4)

/-- The coefficient `g(a, x)` of eq. (6): `−1` if `x > 1`, `0` if `x = 1`. -/
def bellG {MA : ℕ} (x : Fin MA) : ℝ := if x.val ≠ 0 then -1 else 0

/-- The coefficient `h(b, y)` of eq. (6): `−1` if `y > 1`, `0` if `y = 1`. -/
def bellH {MB : ℕ} (y : Fin MB) : ℝ := if y.val ≠ 0 then -1 else 0

/-- The Bell expression `I_{M_A M_B (P+1)(P+1)}` of eq. (6), p. 2, evaluated on a behaviour with
`P + 1` outputs per party (`some a` for `a ∈ {0, …, P − 1}`, `none` for `Φ`):
`∑_{a,b,x,y} f(a,b,x,y) p(a,b|x,y) + ∑_{a,x} g(a,x) p(a|x) + ∑_{b,y} h(b,y) p(b|y)`, the sums over
`a, b` running over the non-empty outputs. The marginals are `marginalA`, `marginalB`. -/
noncomputable def bellValue (P : ℕ) {MA MB : ℕ}
    (p : Option (Fin P) → Option (Fin P) → Fin MA → Fin MB → ℝ) : ℝ :=
  (∑ a : Fin P, ∑ b : Fin P, ∑ x : Fin MA, ∑ y : Fin MB, bellF P a b x y * p (some a) (some b) x y)
    + (∑ a : Fin P, ∑ x : Fin MA, bellG x * marginalA p (some a) x)
    + (∑ b : Fin P, ∑ y : Fin MB, bellH y * marginalB p (some b) y)

/-- The no-signaling behaviour of eq. (13), p. 3: `p^NS(a, b|x, y) = 1/P` if `a + b ≡ xy (mod P)`
and `0` otherwise. -/
noncomputable def witnessBox (P MA MB : ℕ) (a b : Fin P) (x : Fin MA) (y : Fin MB) : ℝ :=
  if bellCong P a b x y then 1 / (P : ℝ) else 0

end BellDetEff.TwoParty


