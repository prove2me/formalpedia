-- Prove2me | Definitions.Def_KramerSaglam_Conditional
-- name    : KramerSaglam_Conditional
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:14.790291+00:00
-- url     : https://prove2.me/theorems/c49962a4-cfec-4f33-95f4-33a95f2d0801
-- title:
--   Entropy, Tsallis entropy, information and progressive entropy of a bit given an arbitrary random variable
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. A **bit** is an event $C\in\mathcal F$, and an observed random variable is a sub-σ-algebra $\mathcal G\subseteq\mathcal F$ (a random variable $Z$ gives $\sigma(Z)$; a pair $Z,W$ gives $\sigma(Z)\vee\sigma(W)$). Write $\mu_{\mathcal G}=P[C\mid\mathcal G]$ for the conditional mean of $C$. Then
--
--   1. $H(C\mid\mathcal G)=\mathbb E\big[H_2(\mu_{\mathcal G})\big]$ and $\bar H(C\mid\mathcal G)=\mathbb E\big[4\mu_{\mathcal G}(1-\mu_{\mathcal G})\big]$;
--   2. $I(C:Z\mid U)=H(C\mid U)-H(C\mid Z,U)$ and $\bar I(C\,;Z\mid U)=\bar H(C\mid U)-\bar H(C\mid Z,U)$;
--   3. the **progressive entropy** given $U$ is
--   $$
--   Q(C\mid U)=\bar I_p\,H(C\mid U)-J_p\,\bar H(C\mid U),
--   $$
--   with $p$ held fixed;
--   4. for two bits, $\mathrm{corr}(B,C)=\mathbb E[(2B-1)(2C-1)]$.
--
--   Unconditional quantities are the case of the trivial σ-algebra. The bit is always the first argument: the paper's $I(B:C\mid U)$ is the information of the bit $B$ about $\sigma(C)$ given $U$, and Tsallis information is not symmetric.
--
--   These definitions realize the paper's convention (p.3) that conditioning on $U$ evaluates a quantity under the conditional law given $U$ and averages over $U$, for observed variables that "may be arbitrary".
--
--   **Formalization Note** The conditional law of a bit is its conditional mean, computed with Mathlib's `condExp`; the tower property gives the paper's "conditional law, then expectation". `condExp` returns $0$ for a σ-algebra that is not contained in $\mathcal F$, so every statement assumes that containment. The identities $I(C:Z\mid U)=H(C\mid U)-H(C\mid Z,U)$ are definitions here; symmetry of Shannon information is a theorem, not used to define anything.
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), §2 pp.2–3 (H̄, Ī, conditioning convention), display (Q) p.1, p.5 and p.13 (d)

import Mathlib
import Definitions.Def_KramerSaglam_Scalars

open MeasureTheory

namespace KramerSaglam

/-!
# Entropy and information of a bit given a σ-algebra

D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), §2, pp.2–3.

**Formalization Note.** The paper's observed variables "may be arbitrary" (p.2). A bit is a
measurable set `C`, and an observed variable `Z` is a sub-σ-algebra (`MeasurableSpace.comap Z _`;
a pair `Z, W` is `Z ⊔ W`). The conditional law given `U` is the conditional mean of `C` given `U`,
and "taking expectation over `U`" (p.3) is the integral. Unconditional quantities are the case
`U = ⊥`. Every statement passes `m ≤ m₀` for the σ-algebras it uses, because `condExp` returns `0`
when this fails.
-/

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-- The conditional mean of the bit `C` given `m`, `P[C = 1 | m]`. -/
noncomputable def condMean (P : Measure Ω) (C : Set Ω) (m : MeasurableSpace Ω) : Ω → ℝ :=
  P[Set.indicator C (fun _ => (1 : ℝ)) | m]

/-- Shannon entropy in bits of `C` given `m`, `H(C | m)`, as the mean of the binary entropy of the
conditional mean. -/
noncomputable def entGiven (P : Measure Ω) (C : Set Ω) (m : MeasurableSpace Ω) : ℝ :=
  ∫ ω, GeneralCK.H (condMean P C m ω) ∂P

/-- Tsallis entropy of `C` given `m`, `H̄(C | m)` (p.2, conditioned as on p.3). -/
noncomputable def tsGiven (P : Measure Ω) (C : Set Ω) (m : MeasurableSpace Ω) : ℝ :=
  ∫ ω, tsallis (condMean P C m ω) ∂P

/-- Shannon information `I(C : Z | U) = H(C | U) − H(C | Z, U)`, with the bit `C` as first argument.
Pass `U = ⊥` for `I(C : Z)`. The paper's `I(B : C | U)` is `info P B (sigma C) U`. -/
noncomputable def info (P : Measure Ω) (C : Set Ω) (Z U : MeasurableSpace Ω) : ℝ :=
  entGiven P C U - entGiven P C (Z ⊔ U)

/-- Tsallis information `Ī(C ; Z | U) = H̄(C | U) − H̄(C | Z, U)` (p.2). It is not symmetric. -/
noncomputable def tsInfo (P : Measure Ω) (C : Set Ω) (Z U : MeasurableSpace Ω) : ℝ :=
  tsGiven P C U - tsGiven P C (Z ⊔ U)

/-- The σ-algebra of a bit used as an observed variable. -/
abbrev sigma (C : Set Ω) : MeasurableSpace Ω := MeasurableSpace.generateFrom {C}

/-- The progressive entropy given `m`, `Q(C | m) = Ī_p H(C | m) − J_p H̄(C | m)` (display (Q), p.1,
and p.3), with `p` held fixed. `Q(C)` is the case `m = ⊥`. -/
noncomputable def qGiven (P : Measure Ω) (p : ℝ) (C : Set Ω) (m : MeasurableSpace Ω) : ℝ :=
  IpBar p * entGiven P C m - Jp p * tsGiven P C m

/-- The correlation `E[(2B − 1)(2C − 1)]` of two bits (pp.5, 13). The integrand is bounded and, for
measurable bits, measurable, so it is integrable. -/
noncomputable def bitCorr (P : Measure Ω) (B C : Set Ω) : ℝ :=
  ∫ ω, (2 * Set.indicator B (fun _ => (1 : ℝ)) ω - 1) *
    (2 * Set.indicator C (fun _ => (1 : ℝ)) ω - 1) ∂P

end KramerSaglam


