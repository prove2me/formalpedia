-- Prove2me | Definitions.Def_PrivGaussMS_Sampler
-- name    : PrivGaussMS_Sampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:11:02.719713+00:00
-- url     : https://prove2.me/theorems/1c2f7b94-4f6f-4697-811c-4de8065b4e90
-- title:
--   Weighted resampling (15), the sampler $\mathcal A$ (Algorithm 4), $\mathcal A_\eta$, $Y_{\mathrm{priv}}$, the proposal, $\Phi_T$ and the corrected output of Lemma B.7
-- statement:
--   For $B\succ0$ in block form with $b>m$, the **candidate batch** is
--   $$Y=1_m\theta^T+\Gamma_b^{1/2}ZC^{1/2},\qquad \Gamma_b=I_m-\tfrac1b1_m1_m^T,$$
--   with $Z$ the first $m$ rows of a uniform $(n-1)\times d$ frame (WeightedResample).
--
--   The **sampler** $\mathcal A$ computes $g,\rho$ and $B$ from the data, draws $V\sim\mathrm{Lap}(2/\varepsilon)$, sets $W=\mathrm{clip}_\ell(V)$, returns $\perp$ if $g+W\ge a_0+\ell$, and otherwise returns a candidate batch for $B$ with fresh randomness. $\mathcal A_\eta$ blanks each output position independently with probability $\eta$ after acceptance and returns the empty partial batch after rejection. $Y_{\mathrm{priv}}$ is $\mathcal A_\eta$ run on the rows of an independent uniform centered frame. The **proposal** takes the first $m$ rows of a uniform centered frame and blanks each position independently with probability $\eta$. For $T\succ0$ with block parameters $(\bar x,S)$, $\Phi_T$ maps each retained vector $z$ to $\bar x+S^{1/2}z$ and keeps the blanks. Finally, given a law of (proposal, decision) $(\zeta,\mathrm{Priv})$, the corrected partial output on input $x$ runs $\mathcal A_\eta(x)$ with fresh randomness if $\mathrm{Priv}=1$, and returns $\Phi_{T(x)}(\zeta)$ if $\mathrm{Priv}=0$ and $T(x)\succ0$, the empty batch otherwise.
--
--   **Formalization Note** Every random object is a pushforward of a product of standard laws, so fresh randomness is a fresh product factor. If the test accepts while $B\not\succ0$ or $b\le m$ (impossible under the paper's parameters, p.40) the sampler returns $\perp$.
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), eq. (15), p.35; Algorithm 3, p.36; Algorithm 4, p.40; §B.4.2, p.44; Lemma B.7, pp.44–45; Algorithm 2, p.33

import Mathlib
import Definitions.Def_PrivGaussMS_Frames
import Definitions.Def_PrivGaussMS_Pruning

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace PrivGaussMS

/-!
# Weighted resampling (15), the sampler `A` (Algorithm 4), omissions, `Y_priv`, the proposal,
# `Φ_T`, and the corrected partial output of Lemma B.7

Moayedi, Yassaee, Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027 submission
(manuscript sha256 1838c582…), eq. (15), p.35; Algorithm 3, p.36; Algorithm 4, p.40; §B.4.2,
p.44; Lemma B.7, pp.44–45; Algorithm 2, p.33.

**Formalization Note.**
* Every random object is the pushforward of a product of the standard laws (uniform frames,
  `Lap(2/ε)`, uniform `[0,1]` coins): "fresh randomness" is a fresh product factor. A position is
  omitted ("with probability `η`") when its coin is `< η`.
* `candidate n m B Z = 1_m θᵀ + Γ_b^{1/2} Z C^{1/2}`, `Γ_b = I_m − b⁻¹ 1_m 1_mᵀ` (15), with `(θ, C, b)`
  the block parameters of `B`; `candidateLaw n m B` is its law for `Z` the first `m` rows of a
  uniform `(n−1) × d` frame (Algorithm 3).
* `samplerAOut` is Algorithm 4 on a fixed Laplace draw `V` and frame `H`. When the test accepts but
  `B ⊁ 0` or `b ≤ m` (which the paper shows cannot happen under its parameters, p.40), the output
  is `⊥` (`none`).
* `samplerAEta` is `A_η` (p.10, p.44): after acceptance each position is blanked independently
  with probability `η`; after rejection the output is the empty partial batch.
* `PhiT T (J, z) = (J, 1 x̄ᵀ + z S^{1/2})` with `(x̄, S)` the block parameters of `T` (p.44).
* `correctedOutput ρ x` is the partial output `v` of Lemma B.7 (Algorithm 2 before the blanks are
  filled) for a decision procedure with joint law `ρ` of `(ζ, Priv)`.
-/

variable {n m d : ℕ}

/-- The candidate batch `Y = 1_m θᵀ + Γ_b^{1/2} Z C^{1/2}` of (15). -/
noncomputable def candidate (m : ℕ) (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (Z : Matrix (Fin m) (Fin d) ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  Matrix.of (fun (_ : Fin m) (j : Fin d) => blockMean B j) +
    CFC.sqrt (1 - (bw B)⁻¹ • Matrix.of (fun (_ : Fin m) (_ : Fin m) => (1 : ℝ))) * Z *
      CFC.sqrt (blockCov B)

/-- The law of the candidate batch (15) / `WeightedResample` (Algorithm 3): `Z` is the first `m`
rows of a uniform `(n − 1) × d` frame. -/
noncomputable def candidateLaw (n m : ℕ) (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Measure (Matrix (Fin m) (Fin d) ℝ) :=
  (uniformFrame (n - 1) d).map fun H => candidate m B (firstRows m H)

open Classical in
/-- Algorithm 4 on the Laplace draw `V` and the frame `H` of `WeightedResample`. -/
noncomputable def samplerAOut (m : ℕ) (lam k a0 : ℕ) (ℓ : ℝ) (x : Fin n → Vec d) (V : ℝ)
    (H : Matrix (Fin (n - 1)) (Fin d) ℝ) : Option (Matrix (Fin m) (Fin d) ℝ) :=
  if (a0 : ℝ) + ℓ ≤ (score x k lam : ℝ) + clip ℓ V then none
  else if (Bstat x k lam).PosDef ∧ (m : ℝ) < bw (Bstat x k lam) then
    some (candidate m (Bstat x k lam) (firstRows m H))
  else none

/-- The sampler `A` (Algorithm 4): `V ∼ Lap(2/ε)`, `W = clip_ℓ(V)`, reject (`⊥`) when
`g + W ≥ a0 + ℓ`, otherwise `WeightedResample(n, m, b, θ, C)` with fresh randomness. -/
noncomputable def samplerA (n m d : ℕ) (lam k a0 : ℕ) (ℓ ε : ℝ) (x : Fin n → Vec d) :
    Measure (Option (Matrix (Fin m) (Fin d) ℝ)) :=
  ((laplace (2 / ε)).prod (uniformFrame (n - 1) d)).map fun p =>
    samplerAOut m lam k a0 ℓ x p.1 p.2

open Classical in
/-- Independent omissions: `⊥` gives the empty partial batch; a batch `Y` keeps row `j` unless
its coin is `< η`. -/
noncomputable def omitBatch (η : ℝ) (Y : Option (Matrix (Fin m) (Fin d) ℝ)) (c : Fin m → ℝ) :
    PartialBatch m d :=
  match Y with
  | none => emptyBatch m d
  | some Y => fun j => if c j < η then none else some (WithLp.toLp 2 (Y j))

/-- `A_η`: run `A`, then omit each output position independently with probability `η` after
acceptance; the empty partial batch after rejection (p.10, p.44). -/
noncomputable def samplerAEta (n m d : ℕ) (lam k a0 : ℕ) (ℓ ε η : ℝ) (x : Fin n → Vec d) :
    Measure (PartialBatch m d) :=
  ((laplace (2 / ε)).prod ((uniformFrame (n - 1) d).prod (coins m))).map fun p =>
    omitBatch η (samplerAOut m lam k a0 ℓ x p.1 p.2.1) p.2.2

/-- The comparison output `Y_priv` (p.44): a uniform centered frame `U₀`, viewed as a dataset,
is fed to `A_η` with fresh randomness. -/
noncomputable def Ypriv (n m d : ℕ) (lam k a0 : ℕ) (ℓ ε η : ℝ) : Measure (PartialBatch m d) :=
  ((uniformCenteredFrame n d).prod
      ((laplace (2 / ε)).prod ((uniformFrame (n - 1) d).prod (coins m)))).map fun p =>
    omitBatch η (samplerAOut m lam k a0 ℓ (rowsOf p.1) p.2.1 p.2.2.1) p.2.2.2

open Classical in
/-- The proposal (p.44): the first `m` rows of a uniform centered frame, each position omitted
independently with probability `η`. -/
noncomputable def proposalLaw (n m d : ℕ) (η : ℝ) : Measure (PartialBatch m d) :=
  ((uniformCenteredFrame n d).prod (coins m)).map fun p =>
    fun j => if p.2 j < η then none else some (WithLp.toLp 2 (firstRows m p.1 j))

/-- `Φ_T(J, z) = (J, 1_{|J|} x̄ᵀ + z S^{1/2})` (p.44), `(x̄, S)` the block parameters of `T`. -/
noncomputable def PhiT (T : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (ζ : PartialBatch m d) :
    PartialBatch m d :=
  fun j => (ζ j).map fun z =>
    WithLp.toLp 2 (blockMean T + CFC.sqrt (blockCov T) *ᵥ WithLp.ofLp z)

/-- The fresh randomness of one call of `A_η`: `V ∼ Lap(2/ε)`, the frame of `WeightedResample`,
and `m` omission coins. -/
noncomputable def freshA (n m d : ℕ) (ε : ℝ) :
    Measure (ℝ × (Matrix (Fin (n - 1)) (Fin d) ℝ × (Fin m → ℝ))) :=
  (laplace (2 / ε)).prod ((uniformFrame (n - 1) d).prod (coins m))

open Classical in
/-- The partial output `v` of Lemma B.7 / Algorithm 2 (before filling blanks) on input `x`, given
the proposal and decision `(ζ, Priv)` and the fresh randomness `r` of `A_η`: if `Priv = 1`, discard
`ζ` and run `A_η` on `x`; if `Priv = 0`, return `Φ_{T(x)}(ζ)` when `T(x) ≻ 0`, else the empty batch. -/
noncomputable def correctedOutputFn (n m d : ℕ) (lam k a0 : ℕ) (ℓ η : ℝ) (x : Fin n → Vec d)
    (q : (PartialBatch m d × Bool) × (ℝ × (Matrix (Fin (n - 1)) (Fin d) ℝ × (Fin m → ℝ)))) :
    PartialBatch m d :=
  if q.1.2 then omitBatch η (samplerAOut m lam k a0 ℓ x q.2.1 q.2.2.1) q.2.2.2
  else if (Tstat x).PosDef then PhiT (Tstat x) q.1.1 else emptyBatch m d

/-- The law of the partial output `v` of Lemma B.7 on input `x`, for a decision procedure with
joint law `ρ` of `(ζ, Priv)`, independent of the fresh randomness of `A_η`. -/
noncomputable def correctedOutput (n m d : ℕ) (lam k a0 : ℕ) (ℓ ε η : ℝ)
    (ρ : Measure (PartialBatch m d × Bool)) (x : Fin n → Vec d) : Measure (PartialBatch m d) :=
  (ρ.prod (freshA n m d ε)).map (correctedOutputFn n m d lam k a0 ℓ η x)

end PrivGaussMS


