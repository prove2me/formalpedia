-- Prove2me | Definitions.Def_LotteryInterm_IID_ValueDist
-- name    : LotteryInterm_IID_ValueDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:07.900383+00:00
-- url     : https://prove2.me/theorems/353c760f-7f72-464a-86d7-ca7c78fb8fee
-- title:
--   Value laws, terminal atoms, virtual values and shifted laws
-- statement:
--   A value law has a finite lower endpoint $a\ge0$, an upper endpoint $b\in[a,+\infty]$, a measurable nonnegative density $f$, positive on $(a,b)$, and optionally a terminal atom of mass $h\le1$ at finite $b$. Its probability measure is exactly the sum of its density on $[a,b)$ and that terminal atom; $h=0$ when $b=+\infty$. The case $a=b$ is permitted.
--
--   Write $S(t)=\Pr[V>t]$. The virtual value and shifted law are
--   $$\phi(t)=t-\frac{S(t)}{f(t)}\quad(a<t<b),\qquad \phi(b)=b,\qquad G_p=\operatorname{Law}((V-p)^+).$$
--   Regularity means that $\phi$ is nondecreasing on the support interior, including the finite terminal endpoint. The vanishing-tail condition is $tS(t)\to0$ as $t\to\infty$. The shifted virtual value uses $G_p((w,\infty))$ and the density $f(w+p)$, with the corresponding terminal convention. The product prior represents independent bidders.
--
--   These definitions retain unbounded supports, atoms, and zero density at the lowest endpoint. Regularity is not tested at a density-free lower endpoint, whose value is a null type unless the law is a pure terminal atom.
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), §3.1–3.2, p.9 (PDF p.10); Appendix A, Lemma A.1 and Definition A.2, p.37 (PDF p.38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Mathlib

open MeasureTheory Filter
open scoped Topology ENNReal

namespace LotteryInterm.IID

/-- Density on a nonnegative interval, with an optional terminal atom. The upper
endpoint may be infinite; lo = hi is allowed and represents a point mass. -/
structure ValueDist where
  lo : ℝ
  hi : WithTop ℝ
  lo_nonneg : 0 ≤ lo
  endpoints : (lo : WithTop ℝ) ≤ hi
  density : ℝ → ℝ
  density_measurable : Measurable density
  density_nonneg : ∀ t, 0 ≤ density t
  density_pos : ∀ t, lo < t → (t : WithTop ℝ) < hi → 0 < density t
  atom : ℝ≥0∞
  atom_le_one : atom ≤ 1
  atom_at_infinity : hi = ⊤ → atom = 0
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  law_eq : law =
    (volume.restrict {t : ℝ | lo ≤ t ∧ (t : WithTop ℝ) < hi}).withDensity
      (fun t => ENNReal.ofReal (density t)) +
    atom • Measure.dirac (hi.untopD 0)

instance (D : ValueDist) : IsProbabilityMeasure D.law := D.probability

noncomputable def survival (D : ValueDist) (t : ℝ) : ℝ :=
  (D.law (Set.Ioi t)).toReal

/-- The finite terminal endpoint has virtual value equal to itself. -/
noncomputable def virtualValue (D : ValueDist) (t : ℝ) : ℝ :=
  if (t : WithTop ℝ) = D.hi then t else t - survival D t / D.density t

def Types (D : ValueDist) : Set ℝ :=
  {t | D.lo ≤ t ∧ (t : WithTop ℝ) ≤ D.hi}

/-- The density formula is required only in the interior; a zero density at
 the lowest endpoint is permitted. A pure terminal point is also permitted. -/
def Regular (D : ValueDist) : Prop :=
  MonotoneOn (virtualValue D) {t | D.lo < t ∧ (t : WithTop ℝ) ≤ D.hi}

def VanishingTail (D : ValueDist) : Prop :=
  Tendsto (fun t : ℝ => t * survival D t) atTop (𝓝 0)

noncomputable def prior {n : ℕ} (D : Fin n → ValueDist) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => (D i).law)

instance {n : ℕ} (D : Fin n → ValueDist) : IsProbabilityMeasure (prior D) := by
  unfold prior
  infer_instance

/-- The shifted law includes its atom at zero. -/
noncomputable def shiftedLaw (D : ValueDist) (p : ℝ) : Measure ℝ :=
  D.law.map (fun t => max (t - p) 0)

/-- Density-version virtual value for the shifted law, including the convention
at a finite terminal atom. The theorem restricts to points with positive density. -/
noncomputable def shiftedVirtual (D : ValueDist) (p w : ℝ) : ℝ :=
  if (w + p : WithTop ℝ) = D.hi then w
  else w - (shiftedLaw D p (Set.Ioi w)).toReal / D.density (w + p)

end LotteryInterm.IID


