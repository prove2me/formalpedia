-- Prove2me | Definitions.Def_RestrictedDec_Supplement_PRF
-- name    : RestrictedDec_Supplement_PRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:27:54.637985+00:00
-- url     : https://prove2.me/theorems/86efbf0a-b051-465c-a6bf-32e4bca8e8d0
-- title:
--   Pseudorandom functions (Definition 5)
-- statement:
--   A **PRF** $P=(\mathrm{PGen},\mathrm{PRF})$ has a seed $k\leftarrow\mathrm{PGen}(1^\lambda)$ and a deterministic $\mathrm{PRF}_k:\mathcal I_\lambda\to\{0,1\}^{\ell_P(\lambda)}$. It is efficient on the domain $\mathcal I$ if seed generation and evaluation are polynomial-time and outputs on $\mathcal I_\lambda$ have length $\ell_P(\lambda)$.
--
--   The advantage of an oracle machine $D$ is
--   $$\mathrm{Adv}^{\mathrm{prf}}_P(D,\lambda)=\Big|\Pr_k[D^{\mathrm{PRF}_k}(1^\lambda)=1]-\Pr_U[D^U(1^\lambda)=1]\Big|,$$
--   with $U$ a uniformly random function on $\mathcal I_\lambda$ sampled consistently (repeated queries get the same answer). $P$ is **secure** if this is negligible for every uniform PPT $D$ making adaptive queries.
--
--   In the CHK compilers the extraction tape of identity $id$ is $\mathrm{PRF}_k(id)$, which fixes one key per identity (Lemma 2).
--
--   **Formalization Note** Queries outside $\mathcal I_\lambda$ are refused.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.2, p.30, Definition 5; Lemma 2, p.31

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_Supplement_interact
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- A **pseudorandom function** `P = (PGen, PRF)`: `gen λ r` is the seed `k ← PGen(1^λ)` on coins
`r`, and `eval λ k x = PRF_k(x)` is deterministic with outputs in `{0,1}^{outLen λ}`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.2, p.30 ("A
pseudorandom function (PRF) P = (PGen, PRF) consists of a probabilistic polynomial-time
key-generation algorithm PGen(1λ), which outputs a seed k, and a deterministic polynomial-time
function PRFk : Iλ −→ {0, 1}rext(λ)"). -/
structure PRF where
  keyCoins : ℕ → ℕ
  outLen : ℕ → ℕ
  gen : (lam : ℕ) → (Fin (keyCoins lam) → Bool) → Str
  eval : ℕ → Str → Str → Str

/-- The PRF is **efficient on the domain `Dom`**: polynomially many seed coins, `PGen` and `PRF`
computed by polynomial-time machines uniformly in `λ` (on generated seeds), and `PRF_k(x)` has
length `outLen λ` for every `x ∈ Dom_λ` (App. A.2, p.30). -/
def PRF.IsEfficient (Dom : ℕ → Str → Prop) (P : PRF) : Prop :=
  NoisyOWMPC.PolyBounded P.keyCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (P.keyCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, List.ofFn r]) = P.gen lam r) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (P.keyCoins lam) → Bool) (x : Str),
    f (BeyondDS.tup [encNat lam, P.gen lam r, x]) = P.eval lam (P.gen lam r) x) ∧
  ∀ lam (r : Fin (P.keyCoins lam) → Bool) (x : Str), Dom lam x →
    (P.eval lam (P.gen lam r) x).length = P.outLen lam

open Classical in
/-- The **challenger of the PRF experiment** (Definition 5). With `real = true` the oracle is
`PRF_k` for the seed `k`; with `real = false` it is a uniformly random function
`U : Dom_λ → {0,1}^{outLen λ}`, sampled consistently (the state is the table of points already
queried). A move `tup [0, x]` is a query, answered with `encOpt (some value)` for `x ∈ Dom_λ` and
refused otherwise; any other move ends the experiment with the guess, the first bit of `fld 1`. -/
noncomputable def PRF.challenger (Dom : ℕ → Str → Prop) (P : PRF) (lam : ℕ) (real : Bool)
    (k : Str) : List (Str × Str) → Str → PMF ((List (Str × Str) × Str) ⊕ Bool)
  | tbl, o =>
    if fld o 0 = [false] then
      if Dom lam (fld o 1) then
        if real then PMF.pure (.inl (tbl, encOpt (some (P.eval lam k (fld o 1)))))
        else
          match tbl.lookup (fld o 1) with
          | some v => PMF.pure (.inl (tbl, encOpt (some v)))
          | none =>
            (PMF.uniformOfFintype (Fin (P.outLen lam) → Bool)).map fun u =>
              .inl ((fld o 1, List.ofFn u) :: tbl, encOpt (some (List.ofFn u)))
      else PMF.pure (.inl (tbl, encOpt none))
    else PMF.pure (.inr ((fld o 1).headD false))

/-- `Adv^prf_P(D, λ) = |Pr_{k ← PGen(1^λ)}[D^{PRF_k}(1^λ) = 1] − Pr_U[D^U(1^λ) = 1]|`
(Definition 5, p.30). -/
noncomputable def PRF.gap (Dom : ℕ → Str → Prop) (P : PRF) (D : Adversary) (lam : ℕ) : ℝ :=
  |(((PMF.uniformOfFintype (Fin (P.keyCoins lam) → Bool)).bind fun r =>
      interact D lam (P.challenger Dom lam true (P.gen lam r)) (D.p.eval lam + 1) [] [] []) true).toReal -
    ((interact D lam (P.challenger Dom lam false []) (D.p.eval lam + 1) [] [] []) true).toReal|

/-- **PRF security** on the domain `Dom` (Definition 5): every uniform PPT oracle machine making
(polynomially many, adaptive) queries has negligible advantage.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 5, App. A.2, p.30
("The PRF is secure if this advantage is negligible for every probabilistic polynomial-time D making
polynomially many adaptive oracle queries. The random function U is sampled consistently"). -/
def PRF.Secure (Dom : ℕ → Str → Prop) (P : PRF) : Prop :=
  ∀ D : Adversary, D.Valid → NoisyOWMPC.Negligible (P.gap Dom D)

end Supplement

end RestrictedDec


