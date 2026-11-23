-- Prove2me | Definitions.Def_CritWinSpin_ForgerScore
-- name    : CritWinSpin_ForgerScore
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:42:01.527369+00:00
-- url     : https://prove2.me/theorems/337079da-fda1-4c65-839e-98eb2d846138
-- title:
--   Fresh-message scan and per-output forging scores for Theorem 7.2
-- statement:
--   For a tuple $X_{1:k}$ and an output tuple $X'_{1:k+1}$, `freshY` implements the deterministic scan of §7: it returns $Y(X'_j)$ at the first coordinate whose message $\\Psi(Y(X'_j))$ is outside $S(X_{1:k})$, and returns $\\bot$ if there is no such coordinate. The predicate `GoodForge` says that a proposed binary configuration $y$ belongs to $\\Omega$ and its message differs from every message $\\Psi(F_t)$.
--
--   The functions `extScore` and `ampScore` split the extension and amplification forging probabilities according to the particular binary configuration $y$ returned by this scan. Splitting by the returned value is useful because the corresponding PPT output events are pairwise disjoint, so their probabilities reassemble by finite additivity.
--
--   **Formalization Note** These definitions package exactly the `List.findSome?` scan and the real-valued scores in the Theorem 7.2 wrapper on p.27; they introduce no probabilistic or computational assumption.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §7, pp.26–27, construction of the forger in the proof of Theorem 7.2.

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- The first decoded configuration whose message is not among the messages decoded from the
training tuple `X`, exactly the scan of §7, p.27. -/
noncomputable def freshY {S : SpinLaw} {n r d k : ℕ} (Ψ : BinCfg n → Fin d → Bool)
    (X : Fin k → Config S (Fin n × Fin r)) (X' : Fin (k + 1) → Config S (Fin n × Fin r)) :
    Option (BinCfg n) :=
  List.findSome? (fun j =>
    match decodeY (X' j) with
    | some y₀ => if ∃ j' : Fin k, decMsg Ψ (X j') = some (Ψ y₀) then none else some y₀
    | none => none) (List.finRange (k + 1))

/-- The output event of a successful fresh forgery against the configurations `Fs`. -/
def GoodForge {n d T : ℕ} (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (Fs : Fin T → BinCfg n) (y : BinCfg n) : Prop :=
  y ∈ Ω ∧ ∀ t, Ψ y ≠ Ψ (Fs t)

open Classical in
/-- The part of the extension forging score returning the particular binary configuration `y`. -/
noncomputable def extScore (S : SpinLaw) (p Ac Cc : ℕ) (slotM : PPT) {n : ℕ}
    (H : Inst n) (û : ℚ) {d T k : ℕ} (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (Fs : Fin T → BinCfg n) (A : PPT) (y : BinCfg n) : ℝ :=
  ∑ ω : Fin T → Option (Config S (Fin n × Fin (cloudSize p Cc n))),
    (∏ t, slotKernel S p Cc slotM H û (Fs t) (ω t)) *
      match lhatRun k ω with
      | none => 0
      | some R =>
        ∑ z : Config S (Fin n × Fin (cloudSize p Cc n)),
          A.prob (tupleCode [encInst (liftInst S p Ac Cc H û),
              encSamples (fun j a => (R j).2 (finProdFinEquiv.symm a))])
            (fun s => decConfig S (n * cloudSize p Cc n) s =
              some (fun a => z (finProdFinEquiv.symm a))) *
          (if freshY Ψ (fun j => (R j).2)
                (Fin.cons z (fun j => (R j).2)) = some y ∧ GoodForge Ω Ψ Fs y then 1 else 0)

open Classical in
/-- The part of the amplification forging score returning the particular configuration `y`. -/
noncomputable def ampScore (S : SpinLaw) (p Ac Cc : ℕ) (slotM : PPT) {n : ℕ}
    (H : Inst n) (û : ℚ) {d T k : ℕ} (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (Fs : Fin T → BinCfg n) (A : PPT) (y : BinCfg n) : ℝ :=
  ∑ ω : Fin T → Option (Config S (Fin n × Fin (cloudSize p Cc n))),
    (∏ t, slotKernel S p Cc slotM H û (Fs t) (ω t)) *
      match lhatRun k ω with
      | none => 0
      | some R =>
        ∑ X' : Fin (k + 1) → Config S (Fin n × Fin (cloudSize p Cc n)),
          A.prob (tupleCode [encInst (liftInst S p Ac Cc H û),
              encSamples (fun j a => (R j).2 (finProdFinEquiv.symm a))])
            (fun s => decTuple S (n * cloudSize p Cc n) (k + 1) s =
              some (fun j a => X' j (finProdFinEquiv.symm a))) *
          (if freshY Ψ (fun j => (R j).2) X' = some y ∧ GoodForge Ω Ψ Fs y then 1 else 0)

end CritWinSpin


