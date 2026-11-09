-- Prove2me | Definitions.Def_RandomQueryXOR_cmi
-- name    : RandomQueryXOR_cmi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:05.644705+00:00
-- url     : https://prove2.me/theorems/14e09ccb-955c-4e72-91f3-9abeb1709f21
-- title:
--   Conditional mutual information $I(X;Y\mid Z)$ of random variables on a finite probability space, and conditioning on an event
-- statement:
--   Let $(\Omega,q)$ be a finite probability space. The probability of an event $E\subseteq\Omega$ is $\Pr[E]=\sum_{\omega\in E}q(\omega)$, and for $\Pr[E]>0$ the **conditioned distribution** is $q(\omega\mid E)=q(\omega)/\Pr[E]$ for $\omega\in E$ and $0$ otherwise.
--
--   For random variables $X,Y,Z$ on $\Omega$ with finite ranges, the **conditional mutual information** (in bits) is
--   $$
--   I(X;Y\mid Z)=H(X\mid Z)-H(X\mid Y,Z),
--   $$
--   computed from the joint law of $(X,Y,Z)$, where $H(X\mid Y)=\sum_y\Pr[Y=y]\,H(X\mid Y=y)$. A tuple of conditioning variables is a single product-valued variable $Z$. The paper's $I(X;Y\mid Z,\mathcal E)$ for an event $\mathcal E$ of positive probability is the conditional mutual information under the distribution conditioned on $\mathcal E$; conditioning on fixed values of variables is conditioning on the event that they take those values.
--
--   **Formalization Note** $I(X;Y\mid Z)$ is the published `WildeQIT.condMutualInfo` of the push-forward of $q$ along $\omega\mapsto(X(\omega),Y(\omega),Z(\omega))$; it is defined as $H(Y\mid Z)-H(Y\mid X,Z)$ with base-2 logarithms, which equals the paper's expression. If $\Pr[E]=0$, Lean's conditioned distribution is the unconditioned $q$ (a junk value never used by the mission's statements).
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Appendix A, p.57 (PDF p.59)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_condMutualInfo

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- The probability `Pr[E] = ∑_{ω ∈ E} q(ω)` of an event `E` on a finite probability space
`(Ω, q)`. -/
noncomputable def probOf {Ω : Type} [Fintype Ω] (q : FinDist Ω) (E : Ω → Prop)
    [DecidablePred E] : ℝ :=
  ∑ ω ∈ Finset.univ.filter E, q.prob ω

/-- The distribution `q(· | E)` conditioned on an event `E` of positive probability:
`q(ω | E) = q(ω) / Pr[E]` for `ω ∈ E` and `0` otherwise (Garg, Sundaresan, Velusamy,
*XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, Appendix A, p.57 =
PDF p.59: "For an event E of positive probability, H(X | E) denotes the entropy of X under the
distribution conditioned on E").

**Formalization Note** If `Pr[E] = 0` the conditioned law is undefined; Lean then returns the
unconditioned law `q` (a junk value). Every statement of the mission conditions only on events
of positive probability (`E_eq` has probability `1/2`; Lemma 5.2 assumes positivity). -/
noncomputable def condDist {Ω : Type} [Fintype Ω] (q : FinDist Ω) (E : Ω → Prop)
    [DecidablePred E] : FinDist Ω :=
  if h : 0 < probOf q E then
    { prob := fun ω => if E ω then q.prob ω / probOf q E else 0
      nonneg := fun ω => by
        split_ifs
        · exact div_nonneg (q.nonneg ω) h.le
        · exact le_rfl
      sum_eq_one := by
        rw [← Finset.sum_filter, ← Finset.sum_div]
        exact div_self h.ne' }
  else q

/-- The conditional mutual information `I(X ; Y | Z)` of three random variables
`X : Ω → α`, `Y : Ω → β`, `Z : Ω → γ` on a finite probability space `(Ω, q)`, in bits
(arXiv:2611.04353, Appendix A, p.57 = PDF p.59: `I(X ; Y | Z) := H(X | Z) − H(X | Y, Z)`).
It is the published `WildeQIT.condMutualInfo` of the joint law of `(X, Y, Z)`.

A tuple of conditioning variables is a product-valued `Z`. Conditioning additionally on an
event `E` (the paper's `I(X ; Y | Z, E)`) is `cmi (condDist q E) X Y Z`; conditioning on fixed
values of variables (the paper's `| Π_{<i} = Π_{<i}, R_pub = R_pub`) is conditioning on the
event that they take those values.

**Formalization Note** `WildeQIT.condMutualInfo` is `H(Y|Z) − H(Y|X,Z)` with base-2 logarithms,
which equals the paper's `H(X|Z) − H(X|Y,Z)` (symmetry of mutual information is a theorem). -/
noncomputable def cmi {Ω α β γ : Type} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (q : FinDist Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) : ℝ :=
  condMutualInfo (q.map fun ω => (X ω, Y ω, Z ω))

end RandomQueryXOR


