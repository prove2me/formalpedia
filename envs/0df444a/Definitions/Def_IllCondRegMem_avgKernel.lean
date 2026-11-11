-- Prove2me | Definitions.Def_IllCondRegMem_avgKernel
-- name    : IllCondRegMem_avgKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:01.098221+00:00
-- url     : https://prove2.me/theorems/2df1651c-c93f-4f41-95b9-e91849713d9b
-- title:
--   The averaged kernel $K_n(x)=\frac{2\phi(\|x\|)}{s_{n-1}\|x\|^{n-1}}$
-- statement:
--   Let $s_{n-1}=2\pi^{n/2}/\Gamma(n/2)$ be the surface area of the unit sphere $S^{n-1}\subseteq\mathbb R^n$. The **averaged kernel** $K_n$ is the signed measure obtained by averaging the measures $\phi(t)\,dt$ on the lines $\mathbb Ru$ over $u\sim\mathrm{Unif}(S^{n-1})$; since $\phi$ is even it has the density
--   $$
--   K_n(x)=\frac{2\phi(\|x\|)}{s_{n-1}\|x\|^{n-1}},\qquad x\ne0 .
--   $$
--   The convolution of a function $f$ on $\mathbb R^n$ with $K_n$ is $(f*K_n)(x)=\int f(x-y)K_n(y)\,dy$. Lemma 14 shows that $K_n$ is stable under translation in $L^1$ and that convolving a pruned mixture density with $K_n$ changes it little.
--
--   **Formalization Note** $K_n$ is defined by its explicit density (22), derived in the paper from the averaging definition; its value at the single point $x=0$ is set to $0$.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 14 and eq. (22), pp.15–16 (PDF pp.16–17)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat
import Definitions.Def_IllCondRegMem_phi

open MeasureTheory

namespace IllCondRegMem

/-- The surface area `s_{n−1} = 2π^{n/2}/Γ(n/2)` of the unit sphere `S^{n−1} ⊆ ℝ^n`. -/
noncomputable def sphereArea (n : ℕ) : ℝ :=
  2 * Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- **Averaged kernel** `K_n` (Lemma 14, eq. (22)).
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), p.15: "K_n
[is] the signed measure obtained by averaging the measures ϕ(t) dt on the lines ℝu over
u ∼ Unif(S^{n−1})"; p.16, eq. (22): "Since ϕ is even, the averaged kernel has explicit density
K_n(x) = 2ϕ(‖x‖)/(s_{n−1}‖x‖^{n−1}), x ≠ 0, where we are using s_{n−1} as the surface area of
S^{n−1}."

`avgKernel n R r` is this density on `ℝ^n`, with the kernel `ϕ` of parameters `R, r`.

**Formalization Note.** `K_n` is defined by its explicit density (22), which the paper derives
from the averaging definition; the value at the single point `x = 0` is set to `0` (a null set). -/
noncomputable def avgKernel (n : ℕ) (R r : ℝ) (x : Vec n) : ℝ :=
  if x = 0 then 0 else 2 * phi R r ‖x‖ / (sphereArea n * ‖x‖ ^ (n - 1))

/-- The convolution `(f ∗ K)(x) = ∫ f(x − y) K(y) dy` on `ℝ^n` (eq. (20), p.15). -/
noncomputable def kconv {n : ℕ} (f K : Vec n → ℝ) (x : Vec n) : ℝ :=
  ∫ y, f (x - y) * K y

end IllCondRegMem


