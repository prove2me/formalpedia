-- Prove2me | Definitions.Def_RobustQSC_avg
-- name    : RobustQSC_avg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:49.327203+00:00
-- url     : https://prove2.me/theorems/c34d58dd-c670-4011-ae64-1be379aa444c
-- title:
--   Averaged local overlap $\mathrm{Avg}_f[g]$
-- statement:
--   For $f,g:\{0,1\}^n\to\mathbb C$,
--
--   $$
--   \mathrm{Avg}_f[g]=\frac1{2n}\sum_{i}\sum_{x}\frac{\bigl|\overline{f(x)}g(x)+\overline{f(x+i)}g(x+i)\bigr|^2}{|f(x)|^2+|f(x+i)|^2}.
--   $$
--
--   The Fourier-side quantity $\mathrm{Avg}_{\hat f}[\hat g]$ is the same formula applied to $\hat f,\hat g$. The factor $\tfrac12$ inside $\tfrac1{2n}$ accounts for the sum over $x$ counting each edge of the hypercube twice. The test's acceptance probability on a pure lab state is the average of these two quantities.
--
--   **Formalization Note** A term with $f(x)=f(x+i)=0$ has denominator $0$ and takes the value $0$ in Lean; its numerator also vanishes, and a Haar-random $f$ vanishes nowhere with probability one. At $n=0$ the prefactor is $0$.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §4, p.21 (display defining Avg_f[g] and Avg_f̂[ĝ])

import Definitions.Def_RobustQSC_fourier

namespace RobustQSC

open QAlgorithms
open scoped ComplexConjugate

/-- The averaged local overlap

$$\mathrm{Avg}_f[g] = \frac1{2n}\sum_{i}\sum_{x}
  \frac{|\overline{f(x)}g(x) + \overline{f(x+i)}g(x+i)|^2}{|f(x)|^2 + |f(x+i)|^2}.$$

`Avg_f̂[ĝ]` is `avg (fourier f) (fourier g)`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §4, p.21 (display defining
`Avg_f[g]` and `Avg_f̂[ĝ]`: "Avg_f[g] := 1/(2n) Σ_i Σ_x |f(x)‾g(x) + f(x+i)‾g(x+i)|² /
(|f(x)|² + |f(x+i)|²)").

**Formalization Note.** A term with `f(x) = f(x+i) = 0` has denominator `0` and Lean's `a/0 = 0`
gives it the value `0`; its numerator is `0` as well, and the paper's Haar-random `f` vanishes
nowhere with probability one. At `n = 0` the prefactor `1/(2n)` is `0`. -/
noncomputable def avg {n : ℕ} (f g : EuclideanSpace ℂ (Qubits n)) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i : Fin n, ∑ x : Qubits n,
    ‖conj (f x) * g x + conj (f (flip x i)) * g (flip x i)‖ ^ 2 /
      (‖f x‖ ^ 2 + ‖f (flip x i)‖ ^ 2)

end RobustQSC


