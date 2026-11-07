-- Prove2me | Definitions.Def_CritWinSpin_errExt
-- name    : CritWinSpin_errExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:40:07.79047+00:00
-- url     : https://prove2.me/theorems/5f71b2a2-77e8-4434-bff6-4e2c2b90d458
-- title:
--   Instance laws and the errors $E_{\mathrm{ext}}(A;k)$, $E_{\mathrm{amp}}(A;k)$
-- statement:
--   Let $M=(J,h)\sim\Pi$ be a random instance on $N$ sites, $X_1,X_2,\dots$ i.i.d. from $\pi_M=\pi^\rho_{J,h}$ given $M$, and $A$ an algorithm receiving $(M,X_{1:k})$. The **sample extension error** and the **sample amplification error** are
--   $$E_{\mathrm{ext}}(A;k)=\mathrm{TV}\bigl(\mathcal L(M,X_{1:k},A(M,X_{1:k})),\ \mathcal L(M,X_{1:k},X_{k+1})\bigr),$$
--   $$E_{\mathrm{amp}}(A;k)=\mathrm{TV}\bigl(\mathcal L(M,A(M,X_{1:k})),\ \mathcal L(M,X'_{1:k+1})\bigr),\quad X'_{1:k+1}\sim\pi_M^{\otimes(k+1)}.$$
--   The first distance is joint with the input samples, so copying a sample does not help. Outputs outside $A^N$, respectively $(A^N)^{k+1}$, count as $\bot$. The law `famLaw` of a PPT family on $1^d$ collects its decoded outputs with their probabilities.
--
--   **Formalization Note** $A$ receives the code of $(M,X_{1:k})$ and its output string is decoded. The kernel forms `errExtKernel`, `errAmpKernel` hold for any stochastic kernel in place of $A$.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §2.2, Definition 2.2, p.9, eqs. (7), (8)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_PPT
import Definitions.Def_CritWinSpin_encInst
open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- A random model instance `M = (J, h) ∼ Π` on `N` sites with finite support (§2.2, p.9). -/
structure InstLaw (N : ℕ) where
  /-- A finite set containing the support of `Π`. -/
  supp : Finset (Inst N)
  /-- The probability `Π(M)`. -/
  prob : Inst N → ℝ

open Classical in
/-- The law on instances of a PPT family `Fam` at `1^d`: the outputs that decode to an instance on
`N` sites, with their probabilities over the coins of `Fam` (§2.2, p.9; Theorem 1.1(ii), p.3). -/
noncomputable def famLaw (Fam : PPT) (N d : ℕ) : InstLaw N where
  supp := (Finset.univ.image fun ω : Fin (Fam.coins.eval (unary d).length) → Bool =>
    decInst N (Fam.alg (tupleCode [List.ofFn ω, unary d]))).eraseNone
  prob := fun M => Fam.prob (unary d) (fun s => decInst N s = some M)

/-- The error (7) of a sample-extension kernel `κ`: the total variation distance between
`L(M, X_{1:k}, κ(M, X_{1:k}))` and `L(M, X_{1:k}, X_{k+1})`, computed **jointly** with `M` and with
the input samples. The third coordinate lives on `A^N ∪ {⊥}`. -/
noncomputable def errExtKernel (S : SpinLaw) {N k : ℕ} (Pi₀ : InstLaw N)
    (κ : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ) : ℝ :=
  tvDist
    (fun w : {M // M ∈ Pi₀.supp} × (Fin k → Config S (Fin N)) × Option (Config S (Fin N)) =>
      Pi₀.prob w.1 * gibbsProd S (castM w.1.1.1) (castV w.1.1.2) w.2.1 * κ w.1 w.2.1 w.2.2)
    (fun w => Pi₀.prob w.1 * gibbsProd S (castM w.1.1.1) (castV w.1.1.2) w.2.1 *
      gibbsOpt S (castM w.1.1.1) (castV w.1.1.2) w.2.2)

/-- The error (8) of a sample-amplification kernel `κ`: the total variation distance between
`L(M, κ(M, X_{1:k}))` and `L(M, X'_{1:k+1})` with `X'_{1:k+1} ∼ π_M^{⊗(k+1)}`. The second coordinate
lives on `(A^N)^{k+1} ∪ {⊥}`. -/
noncomputable def errAmpKernel (S : SpinLaw) {N k : ℕ} (Pi₀ : InstLaw N)
    (κ : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ) : ℝ :=
  tvDist
    (fun w : {M // M ∈ Pi₀.supp} × Option (Fin (k + 1) → Config S (Fin N)) =>
      Pi₀.prob w.1 * ∑ xs : Fin k → Config S (Fin N),
        gibbsProd S (castM w.1.1.1) (castV w.1.1.2) xs * κ w.1 xs w.2)
    (fun w => Pi₀.prob w.1 * gibbsTupleOpt S (castM w.1.1.1) (castV w.1.1.2) (k + 1) w.2)

/-- **The sample extension error `E_ext(A; k)`**, Definition 2.2, eq. (7), p.9, for a PPT algorithm
`A` on the instance law `Pi₀`.

Source: Liu–Zhang–Ren, STOC 2027 submission (manuscript sha256 f77584da…), Definition 2.2, p.9.

**Formalization Note.** `A` receives `tupleCode [encInst M, encSamples X_{1:k}]`; its output string
is decoded by `decConfig`, and any string that is not the code of a configuration counts as `⊥`. -/
noncomputable def errExt (S : SpinLaw) {N : ℕ} (Pi₀ : InstLaw N) (A : PPT) (k : ℕ) : ℝ :=
  errExtKernel S (k := k) Pi₀ fun M xs y =>
    A.prob (tupleCode [encInst M, encSamples xs]) (fun s => decConfig S N s = y)

/-- **The sample amplification error `E_amp(A; k)`**, Definition 2.2, eq. (8), p.9, for a PPT
algorithm `A` on the instance law `Pi₀`. Any output string that is not the code of a `(k+1)`-tuple
counts as `⊥`. -/
noncomputable def errAmp (S : SpinLaw) {N : ℕ} (Pi₀ : InstLaw N) (A : PPT) (k : ℕ) : ℝ :=
  errAmpKernel S (k := k) Pi₀ fun M xs y =>
    A.prob (tupleCode [encInst M, encSamples xs]) (fun s => decTuple S N (k + 1) s = y)

end CritWinSpin


