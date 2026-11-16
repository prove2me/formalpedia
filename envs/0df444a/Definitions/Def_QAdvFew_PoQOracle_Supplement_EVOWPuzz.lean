-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_EVOWPuzz
-- name    : QAdvFew_PoQOracle_Supplement_EVOWPuzz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:21:19.576205+00:00
-- url     : https://prove2.me/theorems/b77d563d-a410-4529-87ec-5d7dad9d3719
-- title:
--   Efficiently verifiable one-way puzzles
-- statement:
--   An **efficiently verifiable one-way puzzle** (EV-OWPuzz, [CGG24]) consists of a QPT sampler $\mathrm{Samp}(1^n)\to(s,k)$ producing a classical puzzle $s$ and answer $k$, and an efficient verification algorithm $\mathrm{Ver}(s,k)$, such that
--
--   1. **correctness:** $\Pr_{(s,k)\leftarrow\mathrm{Samp}(1^n)}[\mathrm{Ver}(s,k)=1]$ is close to $1$, and
--   2. **security:** for every nonuniform QPT adversary $A$, $\Pr_{(s,k)\leftarrow\mathrm{Samp}(1^n)}[\mathrm{Ver}(s,A(s))=1]\le\mathrm{negl}(n)$.
--
--   Theorem B.3 asks for **perfect correctness** (probability exactly $1$ for every $n$) and a classical deterministic polynomial-time verifier; the module's `IsPerfect` is this notion.
--
--   **Formalization Note** The paper cites the notion from [CGG24] without restating it. The adversary chooses its output length (fixed for each $n$).
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem B.3, p. 53 (PDF p. 55); §1.1, p. 4 (PDF p. 6), citing [CGG24]

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_PlainQ
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- A candidate **efficiently verifiable one-way puzzle** with a QPT sampler and a classical
deterministic polynomial-time verifier (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem B.3, p. 53 (PDF p. 55): "EV-OWPuzzs … with perfect
correctness, a QPT sampler, and a classical deterministic polynomial-time verifier"; the notion is
that of [CGG24], which the paper cites without restating): puzzle length `ℓs`, answer length `ℓk`
(polynomials), a sampler `Samp(1^n) → (s, k)` and a verification function `ver`, which accepts
`(s, k)` when `ver (tup [s, k]) = [true]`. -/
structure EVOWPuzz where
  ℓs : Polynomial ℕ
  ℓk : Polynomial ℕ
  samp : QSampler (fun n => ℓs.eval n + ℓk.eval n)
  ver : Str → Str

namespace EVOWPuzz

/-- `Ver(s, a) = 1`. -/
def Accepts (P : EVOWPuzz) (s a : Str) : Prop := P.ver (tup [s, a]) = [true]

open Classical in
/-- `Pr_{(s,k) ← Samp(1^n)}[Ver(s, k) = 1]`. -/
noncomputable def correctProb (P : EVOWPuzz) (n : ℕ) : ℝ :=
  ∑ s : Bits (P.ℓs.eval n), ∑ k : Bits (P.ℓk.eval n),
    P.samp.outProb n (Fin.append s k) * (if P.Accepts (toStr s) (toStr k) then 1 else 0)

open Classical in
/-- `Pr_{(s,k) ← Samp(1^n)}[Ver(s, A(s)) = 1]` for a nonuniform QPT adversary `A`. -/
noncomputable def breakProb (P : EVOWPuzz) (A : NUQAlg (fun n => P.ℓs.eval n)) (n : ℕ) : ℝ :=
  ∑ s : Bits (P.ℓs.eval n), ∑ k : Bits (P.ℓk.eval n), ∑ a : Bits (A.olen n),
    P.samp.outProb n (Fin.append s k) * A.outProb n s a *
      (if P.Accepts (toStr s) (toStr a) then 1 else 0)

/-- The EV-OWPuzz properties with **perfect correctness**: the sampler is uniform QPT, `ver` is
deterministic polynomial-time, `Pr[Ver(s, k) = 1] = 1` at every `n`, and every nonuniform QPT
adversary given `s` finds an accepted answer with negligible probability. -/
def IsPerfect (P : EVOWPuzz) : Prop :=
  P.samp.Uniform ∧ P.samp.PolyBounded ∧ PolyTimeComputable P.ver ∧
  (∀ n : ℕ, P.correctProb n = 1) ∧
  ∀ A : NUQAlg (fun n => P.ℓs.eval n), Negligible (P.breakProb A)

end EVOWPuzz

end QAdvFew.PoQOracle.Supplement


