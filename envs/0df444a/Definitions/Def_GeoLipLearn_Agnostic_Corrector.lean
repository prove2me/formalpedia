-- Prove2me | Definitions.Def_GeoLipLearn_Agnostic_Corrector
-- name    : GeoLipLearn_Agnostic_Corrector
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:07.083186+00:00
-- url     : https://prove2.me/theorems/63295eea-2ed6-4c95-8416-423a17d319e5
-- title:
--   McShane envelope, Gaussian quantile corrector and empirical order statistics
-- statement:
--   The McShane lower envelope is $h(x)=\inf_y(q(y)+\|x-y\|)$. Its agreement constant is
--   $$C_{s,B}=(e^s-1)^{-2}\exp\!\left(\frac{4B^2}{e^{2s}-1}\right).$$
--   For $s>0$ put $c_s=\sigma_s/\rho_s$, where $\rho_s=e^{-s}$ and $\sigma_s=\sqrt{1-e^{-2s}}$. The vote is $q_a[v](x)=\Pr_z[v(\rho_sx+\sigma_sz)\le a]$. For $0<r<1$, let $\psi(r)=\min(2L,c_s[-\Phi^{-1}(r)]_+)$, with $\psi(0)=2L$ and $\psi(1)=0$. The CDF inverse is the published Cohen2019 definition. Then
--   $$R[v](x)=\inf_{a\in[-L,L]}\{a+\psi(q_a[v](x))\},\qquad m_v(x)=\inf\{a:q_a[v](x)\ge1/2\}.$$
--   The stability constant is $K=c_s\sqrt{2\pi}\exp(2L^2/c_s^2)$.
--
--   For $N$ stored probes, sort $u_i=v(\rho_sx+\sigma_sz_i)$ in nondecreasing order and return $\widehat R[v](x)=\min_{1\le j\le N}\{u_{(j)}+\psi(j/N)\}$. Repeated values are retained. The ordinary sample median is the order statistic at zero-based index $\lfloor(N-1)/2\rfloor$. These are explicit constructions, not free functions constrained by their intended properties. **Formalization Note** Real infima are used only for nonempty sets bounded below in the stated regimes; the empirical corrector at $N=0$ is totalized to zero and no milestone invokes that case.
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p.17, Lemma 5.1; pp.20–22, Definition 6.2 and lower median; p.25, Equation (13); p.32, Lemma 8.1

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian
import Definitions.Def_Cohen2019_Robust_Phi

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

noncomputable def mcShane {d : ℕ} (q : Space d → ℝ) (x : Space d) : ℝ :=
  sInf {r : ℝ | ∃ y, r = q y + ‖x-y‖}
noncomputable def witnessConstant (s B : ℝ) : ℝ :=
  (Real.exp s - 1)⁻¹^2 * Real.exp (4*B^2/(Real.exp (2*s)-1))
noncomputable def cs (s : ℝ) : ℝ := sigma s / rho s
noncomputable def penalty (L s r : ℝ) : ℝ :=
  if r ≤ 0 then 2*L else if 1 ≤ r then 0
  else min (2*L) (cs s * max (-Cohen2019.Robust.PhiInvReal r) 0)
noncomputable def vote {d : ℕ} (s : ℝ) (v : Space d → ℝ) (a : ℝ) (x : Space d) : ℝ :=
  (gaussian d).real {z | v (probe s x z) ≤ a}
noncomputable def corrector {d : ℕ} (L s : ℝ) (v : Space d → ℝ) (x : Space d) : ℝ :=
  sInf {r : ℝ | ∃ a ∈ Set.Icc (-L) L, r = a + penalty L s (vote s v a x)}
noncomputable def lowerMedian {d : ℕ} (s : ℝ) (v : Space d → ℝ) (x : Space d) : ℝ :=
  sInf {a : ℝ | 1/2 ≤ vote s v a x}
noncomputable def stabilityConstant (L s : ℝ) : ℝ :=
  cs s * Real.sqrt (2*Real.pi) * Real.exp (2*L^2/(cs s)^2)
noncomputable def sortedValues {N : ℕ} (u : Fin N → ℝ) : List ℝ :=
  (List.ofFn u).mergeSort (fun a b => decide (a ≤ b))
noncomputable def empiricalCorrector {d N : ℕ} (L s : ℝ) (v : Space d → ℝ)
    (z : Fin N → Space d) (x : Space d) : ℝ :=
  let u := sortedValues (fun i => v (probe s x (z i)))
  sInf {r : ℝ | ∃ j : Fin N, r = u[j.val]! + penalty L s ((j.val+1 : ℕ) / (N : ℝ))}
noncomputable def sampleMedian {N : ℕ} (u : Fin N → ℝ) : ℝ :=
  (sortedValues u)[(N-1)/2]!

end GeoLipLearn.Agnostic


