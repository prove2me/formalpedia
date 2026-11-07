-- Prove2me | Definitions.Def_SamplingLLL_Primitives
-- name    : SamplingLLL_Primitives
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:08.012701+00:00
-- url     : https://prove2.me/theorems/c8cc9829-5b5e-4262-a86b-15baaa0a57dc
-- title:
--   Charged rational arithmetic, exact coins and exact coordinate draws
-- statement:
--   Rational operations are charged $(\mathrm{bits}(a)+\mathrm{bits}(b)+1)^2$ on their actual operands $a,b$, where the bit length of $a/b$ in lowest terms is the sum of the sizes of $|a|$ and $b$. The exact coin of bias $p=a/b\in[0,1]$ draws $\lceil\log_2 b\rceil$ fair bits, retries when the resulting number $U$ is at least $b$, and otherwise returns $U<a$; each attempt also costs $\mathrm{bits}(p)$. An exact draw from the coordinate law $\lambda_v$ runs these coins sequentially along $\Omega_v$, conditionally on not having stopped.
--
--   Charging actual operands means the time statements of the mission assert that the rationals stay polynomially long. The planning and verification files prove that the coin has bias exactly $p$ and that the draw has law exactly $\lambda_v$.
--
--   **Formalization Note** The law of these procedures does not depend on the charges.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), §5.1, p.15 ("exact draws from each coordinate law")

import Mathlib
import Definitions.Def_SamplingLLL_Proc
import Definitions.Def_SamplingLLL_AtomicCSP

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

/-- The charge of a rational operation on operands `a`, `b`: `(bits a + bits b + 1)²`, the actual
bit length of the operands, so the time clauses really assert that the numbers stay polynomial. -/
def qcost (a b : ℚ) : ℕ := (bits a + bits b + 1) ^ 2

/-- Charged rational addition. -/
noncomputable def qadd (a b : ℚ) : Proc ℚ := do tick (qcost a b); pure (a + b)
/-- Charged rational subtraction. -/
noncomputable def qsub (a b : ℚ) : Proc ℚ := do tick (qcost a b); pure (a - b)
/-- Charged rational multiplication. -/
noncomputable def qmul (a b : ℚ) : Proc ℚ := do tick (qcost a b); pure (a * b)
/-- Charged rational division (every divisor reached with positive probability is nonzero). -/
noncomputable def qdiv (a b : ℚ) : Proc ℚ := do tick (qcost a b); pure (a / b)
/-- Charged rational comparison. -/
noncomputable def qle (a b : ℚ) : Proc Bool := do tick (qcost a b); pure (decide (a ≤ b))

/-- `k` fair bits read as a number below `2^k`. -/
noncomputable def flipsNat : ℕ → Proc ℕ
  | 0 => pure 0
  | k + 1 => do
    let u ← flipsNat k
    let b ← flip
    pure (2 * u + b.toNat)

/-- The exact coin of bias `p = a/b ∈ [0,1]`: rejection on `⌈log₂ b⌉` fair bits. `U ≥ b` retries;
otherwise the result is `U < a`. Charged `bits p` per attempt plus the flips. -/
noncomputable def ratCoin (p : ℚ) : Proc Bool :=
  loop (fun _ : Unit => do
    tick (bits p)
    let u ← flipsNat (Nat.clog 2 p.den)
    if u < p.den then pure (Sum.inr (decide ((u : ℤ) < p.num))) else pure (Sum.inl ())) ()

/-- Sequential draw along a list of (value, probability), conditional on not having stopped;
`rem` is the remaining mass and `d` the last value. -/
noncomputable def drawList {α : Type} : List (α × ℚ) → α → ℚ → Proc α
  | [], d, _ => pure d
  | (w, pw) :: l, d, rem => do
    let r ← qdiv pw rem
    let b ← ratCoin r
    if b then pure w else do
      let rem' ← qsub rem pw
      drawList l d rem'

namespace ProductCSP

variable {n m : ℕ} (P : ProductCSP n m)

/-- An exact draw from the coordinate law `λ_v`, by sequential `ratCoin` along `Ω_v`. -/
noncomputable def drawCoord (v : Fin n) : Proc (Fin (P.dom v + 1)) :=
  drawList ((List.finRange (P.dom v)).map fun w => (w.castSucc, P.lam v w.castSucc))
    (Fin.last _) 1

/-- Redraw the variables of a list from the product law, keeping all others. -/
noncomputable def redraw : List (Fin n) → P.Config → Proc P.Config
  | [], x => pure x
  | v :: l, x => do
    let w ← P.drawCoord v
    redraw l (Function.update x v w)

/-- The initial draw from `λ`: every variable by `drawCoord`. -/
noncomputable def drawAll : Proc P.Config := P.redraw (List.finRange n) (fun _ => 0)

end ProductCSP

end SamplingLLL


