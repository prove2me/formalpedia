-- Prove2me | Definitions.Def_MIBF_Balanced_PureGap
-- name    : MIBF_Balanced_PureGap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:58:15.674964+00:00
-- url     : https://prove2.me/theorems/a12d5777-2322-42ab-a2a2-8fcf5e6e4a72
-- title:
--   The residual $\kappa$, its entropy-coordinate version $g=\tilde\kappa$ and closure, the perspective bound $L_1=L_4$, the pure gap $G$, and the box $R_S$
-- statement:
--   All quantities are in bits, with $H$, $J$, $\iota$, $F$, $\phi$ as in `GeneralCK_bellman` and $j$ the interior Jeffreys cost.
--
--   **Residual.** For $u,w\in(0,1)$,
--   $$\kappa(u,w)=j(u,w)-F\Bigl(|u-w|,\ \frac{H(u)+H(w)}{2}\Bigr),$$
--   and in entropy coordinates $g(e_1,e_2)=\tilde\kappa(e_1,e_2)=\kappa(\iota(e_1),\iota(e_2))$ for $e_1,e_2\in(0,1]$ (`kappa`, `kappaEnt`).
--
--   **Closure.** The lower-semicontinuous closure of $\tilde\kappa$ from the open square $(0,1)^2$ is the extended-real function on $[0,1]^2$
--   $$\bar\kappa(x)=\liminf_{y\to x,\ y\in(0,1)^2}\tilde\kappa(y)$$
--   (`kappaEntClosure`); the paper records its values $\bar\kappa(0,0)=0$, $\bar\kappa(0,e)=\bar\kappa(e,0)=+\infty$ for $e>0$, $\bar\kappa(e,e)=0$.
--
--   **Perspective extension.** $F$ is extended evenly in $s$ and lower-semicontinuously: $F(0,e)=0$ for $e\ge0$ and $F(s,0)=+\infty$ for $s\ne0$ (`FExt`).
--
--   **Four-moment bound.** For a four-moment tuple $M=(\mu_u,\mu_w,e_u,e_w)$,
--   $$L_1(M)=L_4(M)=F\Bigl(|\mu_w-\mu_u|,\ \frac{e_u+e_w}{2}\Bigr)+\bar\kappa(e_u,e_w)\in(-\infty,+\infty]$$
--   (`L4`).
--
--   **Pure gap.** At positive entropy coordinates $e_u,e_w>0$,
--   $$G(M)=L_4(M)-R_\phi(M)=F\Bigl(|\mu_w-\mu_u|,\ \frac{e_u+e_w}{2}\Bigr)+\tilde\kappa(e_u,e_w)-R_\phi(M)\in\mathbb R$$
--   (`pureGap`).
--
--   **Retained box.** With the seam constant $S=10^{-4}$ (`seamS`),
--   $$R_S=\Bigl\{(a,c,e,f):\ 0\le a\le c\le\tfrac12,\ a+c\ge S,\ 0<e\le H(a),\ 0<f\le H(c)\Bigr\},$$
--   a point of which is the tuple $(\mu_u,\mu_w,e_u,e_w)=(a,c,e,f)$ (`InRS`).
--
--   The pure gap $G$ is an explicit function of the four moments; since $\zeta\ge L_4$, the inequality $G\ge0$ is a sufficient condition for the balanced Bellman inequality $\zeta\ge R_\phi$.
--
--   **Formalization Note** `pureGap` uses the real functions $F$ and $\tilde\kappa$ directly; at positive entropies these are the paper's values (no closure or $+\infty$ is involved). `L4` is the extended-real version used at every four-moment tuple, including zero entropies. Off their stated domains the published `GeneralCK` functions return junk values (e.g. `GeneralCK.F s 0 = s·J(0) = 0`), which is why the extended `FExt` and the closure are defined here.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 7, eq. (7), p. 10, eqs. (19)–(20); [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 10 (PDF 32), eq. (11) extension, [Full] p. 11 (PDF 33), eqs. (15)–(17), [Full] p. 13 (PDF 35), S = 10⁻⁴, [Full] p. 29 (PDF 51), R_S

import Mathlib
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_MIBF_Balanced_BellmanDifference

namespace MIBF.Balanced

/-- The residual `κ(u, w) = j(u, w) - F(|u - w|, (H(u) + H(w))/2)` (bits), for interior
points `u, w ∈ (0, 1)`. -/
noncomputable def kappa (u w : ℝ) : ℝ :=
  GeneralCK.interiorCost u w - GeneralCK.F |u - w| ((GeneralCK.H u + GeneralCK.H w) / 2)

/-- The residual in entropy coordinates, `g(e₁, e₂) = κ(ι(e₁), ι(e₂))`, with `ι` the lower
inverse of the binary entropy (bits); used at positive entropies `e₁, e₂ ∈ (0, 1]`. -/
noncomputable def kappaEnt (e1 e2 : ℝ) : ℝ :=
  kappa (GeneralCK.entropyInverse e1) (GeneralCK.entropyInverse e2)

/-- The lower-semicontinuous closure of `kappaEnt` from the open square `(0,1)²`,
an extended-real function on the closed square `[0,1]²`:
`closure(x) = liminf_{y → x, y ∈ (0,1)²} kappaEnt(y)`. -/
noncomputable def kappaEntClosure (e1 e2 : ℝ) : EReal :=
  Filter.liminf (fun p : ℝ × ℝ => ((kappaEnt p.1 p.2 : ℝ) : EReal))
    (nhdsWithin (e1, e2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1))

/-- The perspective `F` with its even and lower-semicontinuous extension:
`F(0, e) = 0`, `F(s, 0) = +∞` for `s ≠ 0`, and `F(s, e) = GeneralCK.F |s| e` otherwise. -/
noncomputable def FExt (s e : ℝ) : EReal :=
  if s = 0 then 0 else if e = 0 then ⊤ else ((GeneralCK.F |s| e : ℝ) : EReal)

/-- The four-moment (perspective) lower bound with boundary conventions,
`L₁(M) = L₄(M) = F(|mw - mu|, (eu + ew)/2) + closure(eu, ew)`, extended-real valued. -/
noncomputable def L4 (mu mw eu ew : ℝ) : EReal :=
  FExt |mw - mu| ((eu + ew) / 2) + kappaEntClosure eu ew

/-- The pure gap `G = L₄ - R_ϕ` at positive entropy coordinates (real valued):
`G = F(|mw - mu|, (eu + ew)/2) + g(eu, ew) - R_ϕ(mu, mw, eu, ew)`. -/
noncomputable def pureGap (mu mw eu ew : ℝ) : ℝ :=
  GeneralCK.F |mw - mu| ((eu + ew) / 2) + kappaEnt eu ew - Rphi mu mw eu ew

/-- The seam constant `S = 10⁻⁴`. -/
noncomputable def seamS : ℝ := 1 / 10000

/-- Membership of `(a, c, e, f)` in the box
`R_S = {0 ≤ a ≤ c ≤ 1/2, a + c ≥ S, 0 < e ≤ H(a), 0 < f ≤ H(c)}`. -/
def InRS (a c e f : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ c ∧ c ≤ 1 / 2 ∧ seamS ≤ a + c ∧
    0 < e ∧ e ≤ GeneralCK.H a ∧ 0 < f ∧ f ≤ GeneralCK.H c

end MIBF.Balanced


