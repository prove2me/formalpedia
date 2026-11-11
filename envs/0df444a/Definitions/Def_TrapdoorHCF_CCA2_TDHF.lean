-- Prove2me | Definitions.Def_TrapdoorHCF_CCA2_TDHF
-- name    : TrapdoorHCF_CCA2_TDHF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T19:32:19.881772+00:00
-- url     : https://prove2.me/theorems/401e9ef8-f093-45ef-817f-0f13dd9160a6
-- title:
--   Trapdoor hardcore functions: syntax, efficiency and perfect correctness
-- statement:
--   A **trapdoor hardcore function** has key generation, a sampler for its input distribution, deterministic public evaluation, deterministic designated-value evaluation, and deterministic partial inversion using the secret key. For parameter $\lambda$, keys and sampled inputs are strings; the designated value has length $l(\lambda)$ and partial inversion returns either such a string or $\perp$.
--
--   Efficiency requires polynomially bounded output length and coin counts, and one uniform polynomial-time machine for each algorithm on its stated domain. Partial inversion is defined on every string. Perfect correctness asserts, for every generated key pair and every sampled input $x$,
--
--   $$\operatorname{pInv}(sk,\operatorname{Eval}(pk,x))=\operatorname{hEval}(pk,x).$$
--
--   The input space is represented by the range of a polynomial-time sampler on uniform coins, and sampling means its output distribution. This generalizes the source's uniform, efficiently recognizable input spaces by dropping recognizability and allowing nonuniform sampler laws. No injectivity or off-image failure is required. Bit strings, explicit finite coin vectors, tuple codes, and an optional string for failure supply the encoding. These definitions provide the common interface for both constructions and all security experiments.
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Definitions 8–9 and section preamble, p.15

import Mathlib
import Definitions.Def_RestrictedDec_PKE_IsScheme
import Definitions.Def_RestrictedDec_PolyParam
import Definitions.Def_RestrictedDec_Adversary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Definition 8, p.15. The input distribution is specified by an explicit sampler.
All algorithms are raw data; no correctness or security is built into this record. -/
structure TDHF where
  keyCoins : ℕ → ℕ
  keyGen : (lam : ℕ) → (Fin (keyCoins lam) → Bool) → Str × Str
  sampCoins : ℕ → ℕ
  samp : (lam : ℕ) → (Fin (sampCoins lam) → Bool) → Str
  eval : ℕ → Str → Str → Str
  hEval : ℕ → Str → Str → Str
  pInv : ℕ → Str → Str → Option Str

/-- Uniform explicit coins, including the unique empty vector when k = 0. -/
noncomputable def coinsLaw (k : ℕ) : PMF (Fin k → Bool) := PMF.uniformOfFintype _

noncomputable def TDHF.keyLaw (T : TDHF) (lam : ℕ) : PMF (Str × Str) :=
  (coinsLaw (T.keyCoins lam)).map (T.keyGen lam)

noncomputable def TDHF.inputLaw (T : TDHF) (lam : ℕ) : PMF Str :=
  (coinsLaw (T.sampCoins lam)).map (T.samp lam)

/-- Definition 8 and its section preamble, p.15. Uniform polynomial time on the
source's input domains; pInv is total on strings and returns l bits or failure.
The sampler model generalizes uniform efficiently recognizable input spaces. -/
def TDHF.IsScheme (l : ℕ → ℕ) (T : TDHF) : Prop :=
  NoisyOWMPC.PolyBounded l ∧
  NoisyOWMPC.PolyBounded T.keyCoins ∧ NoisyOWMPC.PolyBounded T.sampCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (r : Fin (T.keyCoins lam) → Bool),
      f (BeyondDS.tup [encNat lam, List.ofFn r]) =
        BeyondDS.tup [(T.keyGen lam r).1, (T.keyGen lam r).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (c : Fin (T.sampCoins lam) → Bool),
      f (BeyondDS.tup [encNat lam, List.ofFn c]) = T.samp lam c) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (r : Fin (T.keyCoins lam) → Bool) (c : Fin (T.sampCoins lam) → Bool),
      f (BeyondDS.tup [encNat lam, (T.keyGen lam r).1, T.samp lam c]) =
        T.eval lam (T.keyGen lam r).1 (T.samp lam c)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (r : Fin (T.keyCoins lam) → Bool) (c : Fin (T.sampCoins lam) → Bool),
      f (BeyondDS.tup [encNat lam, (T.keyGen lam r).1, T.samp lam c]) =
        T.hEval lam (T.keyGen lam r).1 (T.samp lam c)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (r : Fin (T.keyCoins lam) → Bool) (y : Str),
      f (BeyondDS.tup [encNat lam, (T.keyGen lam r).2, y]) =
        RestrictedDec.encOpt (T.pInv lam (T.keyGen lam r).2 y)) ∧
  (∀ lam (r : Fin (T.keyCoins lam) → Bool) (c : Fin (T.sampCoins lam) → Bool),
    (T.hEval lam (T.keyGen lam r).1 (T.samp lam c)).length = l lam) ∧
  (∀ lam (r : Fin (T.keyCoins lam) → Bool) (y z : Str),
    T.pInv lam (T.keyGen lam r).2 y = some z → z.length = l lam)

/-- Definition 9, p.15: all generated keys and every input in the sampler's range. -/
def TDHF.PerfectlyCorrect (T : TDHF) : Prop :=
  ∀ lam (r : Fin (T.keyCoins lam) → Bool) (c : Fin (T.sampCoins lam) → Bool),
    T.pInv lam (T.keyGen lam r).2 (T.eval lam (T.keyGen lam r).1 (T.samp lam c)) =
      some (T.hEval lam (T.keyGen lam r).1 (T.samp lam c))

end TrapdoorHCF.CCA2


