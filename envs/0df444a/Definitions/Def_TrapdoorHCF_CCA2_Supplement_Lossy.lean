-- Prove2me | Definitions.Def_TrapdoorHCF_CCA2_Supplement_Lossy
-- name    : TrapdoorHCF_CCA2_Supplement_Lossy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:40:43.50724+00:00
-- url     : https://prove2.me/theorems/4fb0d8d4-3e58-4634-95e5-c5fdbd1e62ba
-- title:
--   Lossy trapdoor hardcore functions, lossy public-key encryption, fiber sampling and the Appendix C constructions
-- statement:
--   This file fixes the lossy notions of Sections 3 and 6 and Appendix C.
--
--   1. **Lossy trapdoor hardcore function** (Definitions 12–16). A TDHF $(\mathrm{KGen}_{rec},\mathrm{Eval},\mathrm{hEval},\mathrm{pInv})$ together with a lossy key generator $\mathrm{KGen}_{los}(1^\lambda)\to pk_{los}$ that outputs no trapdoor. $\mathrm{Eval}$ and $\mathrm{hEval}$ are single polynomial-time algorithms used under keys of either mode, and $\mathrm{hEval}$ outputs $l(\lambda)$ bits in both modes. Perfect correctness is the TDHF condition for recoverable keys. *Mode indistinguishability*: no uniform PPT adversary given $(1^\lambda,pk)$ distinguishes a recoverable from a lossy public key with non-negligible advantage. *Statistical lossiness*: there is one negligible $\varepsilon$ with
--   $$\Delta\bigl((\mathrm{Eval}(pk,X),\mathrm{hEval}(pk,X)),\ (\mathrm{Eval}(pk,X),U)\bigr)\le\varepsilon(\lambda)$$
--   for every $\lambda$ and every lossy key $pk$ in the support of $\mathrm{KGen}_{los}(1^\lambda)$, where $X\leftarrow D_\lambda$ and $U\leftarrow\{0,1\}^{l(\lambda)}$ are independent. *Secure* means perfectly correct, mode indistinguishable and statistically lossy.
--
--   2. **Fiber sampling** (Definitions 17–19). A fiber sampler $\mathrm{FSamp}(pk,z;r)$, $z\in\{0,1\}^{l(\lambda)}$, $r\in\{0,1\}^{s(\lambda)}$ with $s$ polynomially bounded, is one polynomial-time algorithm on every valid key of either mode; its outputs are inputs in $D_\lambda$; *fiber consistency* $\mathrm{hEval}(pk,\mathrm{FSamp}(pk,z;r))=z$ holds for every valid key, label and coins; *distributional fidelity* asks, for each mode, that $(pk,\mathrm{FSamp}(pk,Z;R))$ and $(pk,X)$ have negligible statistical distance. *Fiber hiding*: there is one negligible $\varepsilon$ with $\Delta(Y_{pk,z_0},Y_{pk,z_1})\le\varepsilon(\lambda)$ for all $\lambda$, lossy keys and labels, where $Y_{pk,z}=\mathrm{Eval}(pk,\mathrm{FSamp}(pk,z;R))$.
--
--   3. **Lossy public-key encryption** (Definition 7). A PKE $(\mathrm{Gen}_{inj},\mathrm{Enc},\mathrm{Dec})$ with a lossy key generator $\mathrm{Gen}_{lossy}$; $\mathrm{Enc}$ is one polynomial-time algorithm under keys of either mode. Perfect correctness is Definition 1 for recoverable keys. Security is mode indistinguishability together with *ciphertext lossiness*: one negligible $\varepsilon$ with $\Delta(\mathrm{Enc}(pk,m_0;R_0),\mathrm{Enc}(pk,m_1;R_1))\le\varepsilon(\lambda)$ for every $\lambda$, lossy key and pair of messages in $\{0,1\}^{n(\lambda)}$, with independent uniform $R_0,R_1$.
--
--   4. **Constructions.** Section C.1: the Section A.1 scheme on the recoverable part of an LTDHF, with its lossy key generator. Section C.2: the Section A.2 function ($x=m\Vert r$, $\mathrm{Eval}=\mathrm{Enc}$, $\mathrm{hEval}=m$, $\mathrm{pInv}=\mathrm{Dec}$) on a lossy PKE, with its lossy key generator.
--
--   These definitions are the vocabulary of Theorems 4, 9, 10 and 11 and Lemmas 8 and 12.
--
--   **Formalization Note** The input space $D_\lambda$ is the range of the explicit sampler of the base TDHF definition, so "outputs in $D_\lambda$" is membership in that range. Lossy keys are written as the lossy generator applied to each coin vector, which is the same set as its support.
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Definition 7, p.14; Definitions 12–16, pp.22–23; Definitions 17–19, p.25; Sections C.1–C.2, pp.47–50

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_CPA
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- One oracle-free stage on `(1^λ, pk)` with `pk` drawn from `pkLaw λ`; the first output bit
is the guess and exhaustion outputs 0. Used for mode indistinguishability (Definitions 7, 14). -/
noncomputable def expKey (A : RestrictedDec.Adversary) (pkLaw : ℕ → PMF Str) (lam : ℕ) :
    PMF Bool := do
  let pk ← pkLaw lam
  let r ← runStage A lam (fun _ => none) (A.p.eval lam + 1) [] (BeyondDS.tup [encNat lam, pk])
  pure ((r.output.getD []).headD false)

/-- `{pk_rec}_λ ≈c {pk_los}_λ` against uniform PPT adversaries. -/
def KeysIndist (recLaw losLaw : ℕ → PMF Str) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible (advantage (expKey A recLaw) (expKey A losLaw))

/-! ## Lossy trapdoor hardcore functions (Definitions 12–19, pp.22–25) -/

/-- Definition 12, p.22. The `TDHF` part's key generation is `KGen_rec`; `losKeyGen` is
`KGen_los`, which outputs only a public key. `eval` and `hEval` are used under keys of either
mode; `pInv` only under recoverable trapdoors. -/
structure LTDHF extends TDHF where
  losCoins : ℕ → ℕ
  losKeyGen : (lam : ℕ) → (Fin (losCoins lam) → Bool) → Str

/-- Law of the recoverable-mode public key. -/
noncomputable def LTDHF.recPkLaw (T : LTDHF) (lam : ℕ) : PMF Str :=
  (T.keyLaw lam).map Prod.fst

/-- Law of `pk_los ← KGen_los(1^λ)`. -/
noncomputable def LTDHF.losPkLaw (T : LTDHF) (lam : ℕ) : PMF Str :=
  (coinsLaw (T.losCoins lam)).map (T.losKeyGen lam)

/-- A valid public key: in the support of either key generator. -/
def LTDHF.ValidPk (T : LTDHF) (lam : ℕ) (pk : Str) : Prop :=
  (∃ r, (T.keyGen lam r).1 = pk) ∨ ∃ r, T.losKeyGen lam r = pk

/-- Definition 12 and the §6.1 preamble, p.22: the recoverable part is an efficient TDHF;
lossy key generation is uniform polynomial time on polynomially many coins; one polynomial-time
machine computes `Eval` (resp. `hEval`) on every valid key of either mode and every input of
`D_λ`; `hEval` outputs `l(λ)` bits under lossy keys too. -/
def LTDHF.IsScheme (l : ℕ → ℕ) (T : LTDHF) : Prop :=
  T.toTDHF.IsScheme l ∧ NoisyOWMPC.PolyBounded T.losCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (r : Fin (T.losCoins lam) → Bool),
      f (BeyondDS.tup [encNat lam, List.ofFn r]) = T.losKeyGen lam r) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (pk : Str), T.ValidPk lam pk → ∀ c : Fin (T.sampCoins lam) → Bool,
      f (BeyondDS.tup [encNat lam, pk, T.samp lam c]) = T.eval lam pk (T.samp lam c)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (pk : Str), T.ValidPk lam pk → ∀ c : Fin (T.sampCoins lam) → Bool,
      f (BeyondDS.tup [encNat lam, pk, T.samp lam c]) = T.hEval lam pk (T.samp lam c)) ∧
  (∀ lam (r : Fin (T.losCoins lam) → Bool) (c : Fin (T.sampCoins lam) → Bool),
    (T.hEval lam (T.losKeyGen lam r) (T.samp lam c)).length = l lam)

/-- Definition 14, p.23: indistinguishable modes. -/
def LTDHF.ModeIndist (T : LTDHF) : Prop := KeysIndist T.recPkLaw T.losPkLaw

/-- Law of `(Eval(pk,X), hEval(pk,X))`, `X ← D_λ`. -/
noncomputable def LTDHF.realPair (T : LTDHF) (lam : ℕ) (pk : Str) : PMF (Str × Str) :=
  (T.inputLaw lam).map fun x => (T.eval lam pk x, T.hEval lam pk x)

/-- Law of `(Eval(pk,X), U)`, `X ← D_λ` and `U ← {0,1}^{l(λ)}` independent. -/
noncomputable def LTDHF.randPair (l : ℕ → ℕ) (T : LTDHF) (lam : ℕ) (pk : Str) :
    PMF (Str × Str) := do
  let x ← T.inputLaw lam
  let u ← coinsLaw (l lam)
  pure (T.eval lam pk x, List.ofFn u)

/-- Definition 15, p.23: one negligible `ε` bounds the distance for every `λ` and every lossy
public key in the support of `KGen_los(1^λ)`. -/
def LTDHF.StatLossy (l : ℕ → ℕ) (T : LTDHF) : Prop :=
  ∃ ε : ℕ → ℝ, NoisyOWMPC.Negligible ε ∧
    ∀ lam (r : Fin (T.losCoins lam) → Bool),
      sd (T.realPair lam (T.losKeyGen lam r)) (T.randPair l lam (T.losKeyGen lam r)) ≤ ε lam

/-- Definition 16, p.23: "A perfectly correct LTDHF is secure if" it has indistinguishable modes
and is statistically lossy. Perfect correctness (Definition 13) is recoverable-mode only. -/
def LTDHF.Secure (l : ℕ → ℕ) (T : LTDHF) : Prop :=
  T.toTDHF.PerfectlyCorrect ∧ T.ModeIndist ∧ T.StatLossy l

/-- Definition 17, p.25, distributional fidelity: `Δ((pk, FSamp(pk,Z;R)), (pk, X))` with `pk`
from `pkLaw`, `Z ← {0,1}^{l(λ)}`, `R ← {0,1}^{s(λ)}` and `X ← D_λ`, all independent. -/
noncomputable def fidelityGap (l s : ℕ → ℕ) (T : LTDHF)
    (fsamp : (lam : ℕ) → Str → Str → (Fin (s lam) → Bool) → Str)
    (pkLaw : ℕ → PMF Str) (lam : ℕ) : ℝ :=
  sd (do
      let pk ← pkLaw lam
      let z ← coinsLaw (l lam)
      let r ← coinsLaw (s lam)
      pure (pk, fsamp lam pk (List.ofFn z) r))
    (do
      let pk ← pkLaw lam
      let x ← T.inputLaw lam
      pure (pk, x))

/-- Definition 17, p.25: `FSamp(pk, z; r)` with `z ∈ {0,1}^{l(λ)}`, `r ∈ {0,1}^{s(λ)}`, in both
key modes: polynomially many coins; one polynomial-time machine on every valid key, label and
coins; outputs in `D_λ` (the sampler's range); fiber consistency `hEval(pk, FSamp(pk,z;r)) = z`;
and distributional fidelity `(pk, FSamp(pk,Z;R)) ≈s (pk, X)` for each mode. -/
def FiberSamplable (l s : ℕ → ℕ) (T : LTDHF)
    (fsamp : (lam : ℕ) → Str → Str → (Fin (s lam) → Bool) → Str) : Prop :=
  NoisyOWMPC.PolyBounded s ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (pk : Str), T.ValidPk lam pk → ∀ z : Str, z.length = l lam →
      ∀ r : Fin (s lam) → Bool,
        f (BeyondDS.tup [encNat lam, pk, z, List.ofFn r]) = fsamp lam pk z r) ∧
  (∀ lam (pk : Str), T.ValidPk lam pk → ∀ z : Str, z.length = l lam →
    ∀ r : Fin (s lam) → Bool, ∃ c : Fin (T.sampCoins lam) → Bool,
      T.samp lam c = fsamp lam pk z r) ∧
  (∀ lam (pk : Str), T.ValidPk lam pk → ∀ z : Str, z.length = l lam →
    ∀ r : Fin (s lam) → Bool, T.hEval lam pk (fsamp lam pk z r) = z) ∧
  NoisyOWMPC.Negligible (fidelityGap l s T fsamp T.recPkLaw) ∧
  NoisyOWMPC.Negligible (fidelityGap l s T fsamp T.losPkLaw)

/-- Definition 18, p.25: `Y_{pk,z} := Eval(pk, FSamp(pk, z; R))`, `R ← {0,1}^{s(λ)}`; one
negligible `ε` bounds `Δ(Y_{pk,z0}, Y_{pk,z1})` for every `λ`, lossy key and labels. -/
noncomputable def fiberLaw (s : ℕ → ℕ) (T : LTDHF)
    (fsamp : (lam : ℕ) → Str → Str → (Fin (s lam) → Bool) → Str)
    (lam : ℕ) (pk z : Str) : PMF Str :=
  (coinsLaw (s lam)).map fun r => T.eval lam pk (fsamp lam pk z r)

def FiberHiding (l s : ℕ → ℕ) (T : LTDHF)
    (fsamp : (lam : ℕ) → Str → Str → (Fin (s lam) → Bool) → Str) : Prop :=
  ∃ ε : ℕ → ℝ, NoisyOWMPC.Negligible ε ∧
    ∀ lam (r : Fin (T.losCoins lam) → Bool) (z0 z1 : Str),
      z0.length = l lam → z1.length = l lam →
      sd (fiberLaw s T fsamp lam (T.losKeyGen lam r) z0)
        (fiberLaw s T fsamp lam (T.losKeyGen lam r) z1) ≤ ε lam

/-! ## Lossy public-key encryption (Definition 7, p.14) -/

/-- Definition 7, p.14. The `PKE` part's key generation is `Gen_inj`; `losKeyGen` is
`Gen_lossy`, which outputs only a public key. `enc` is used under keys of either mode; `dec`
only under recoverable secret keys. -/
structure LPKE extends RestrictedDec.PKE where
  losCoins : ℕ → ℕ
  losKeyGen : (lam : ℕ) → (Fin (losCoins lam) → Bool) → Str

noncomputable def LPKE.recPkLaw (P : LPKE) (lam : ℕ) : PMF Str :=
  (P.keyLaw lam).map Prod.fst

noncomputable def LPKE.losPkLaw (P : LPKE) (lam : ℕ) : PMF Str :=
  (coinsLaw (P.losCoins lam)).map (P.losKeyGen lam)

def LPKE.ValidPk (P : LPKE) (lam : ℕ) (pk : Str) : Prop :=
  (∃ r, (P.keyGen lam r).1 = pk) ∨ ∃ r, P.losKeyGen lam r = pk

/-- Definition 7, p.14 and §3.2, p.10: the recoverable part is an efficient PKE with message
space `{0,1}^{n(λ)}`; lossy key generation is uniform polynomial time on polynomially many coins;
one polynomial-time machine computes `Enc` under every valid key of either mode. -/
def LPKE.IsScheme (n : ℕ → ℕ) (P : LPKE) : Prop :=
  P.toPKE.IsScheme n ∧ NoisyOWMPC.PolyBounded P.losCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (r : Fin (P.losCoins lam) → Bool),
      f (BeyondDS.tup [encNat lam, List.ofFn r]) = P.losKeyGen lam r) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ lam (pk : Str), P.ValidPk lam pk → ∀ (m : Str), m.length = n lam →
      ∀ ρ : Fin (P.encCoins lam) → Bool,
        f (BeyondDS.tup [encNat lam, pk, m, List.ofFn ρ]) = P.enc lam pk m ρ)

/-- Definition 7, p.14: perfect correctness in the recoverable mode (Definition 1's form). -/
def LPKE.PerfectlyCorrect (n : ℕ → ℕ) (P : LPKE) : Prop :=
  PKE.PerfectlyCorrect n P.toPKE

def LPKE.ModeIndist (P : LPKE) : Prop := KeysIndist P.recPkLaw P.losPkLaw

/-- Definition 7, p.14: one negligible `ε` with `Δ(Enc(pk,m0;R0), Enc(pk,m1;R1)) ≤ ε(λ)` for
every `λ`, lossy key in the support of `Gen_lossy(1^λ)` and messages `m0, m1 ∈ {0,1}^{n(λ)}`,
with `R0, R1` independent uniform coins. -/
def LPKE.CiphertextLossy (n : ℕ → ℕ) (P : LPKE) : Prop :=
  ∃ ε : ℕ → ℝ, NoisyOWMPC.Negligible ε ∧
    ∀ lam (r : Fin (P.losCoins lam) → Bool) (m0 m1 : Str),
      m0.length = n lam → m1.length = n lam →
      sd (P.encLaw lam (P.losKeyGen lam r) m0) (P.encLaw lam (P.losKeyGen lam r) m1) ≤ ε lam

/-- Definition 7, p.14: the two security properties; perfect correctness is stated beside it. -/
def LPKE.Secure (n : ℕ → ℕ) (P : LPKE) : Prop :=
  P.ModeIndist ∧ P.CiphertextLossy n

/-! ## The Appendix C constructions -/

/-- Section C.1, pp.47–48: the Section A.1 scheme on the recoverable part, with the LTDHF's
lossy key generator. Encryption randomness is an input of `D_λ`. -/
def lpkeOfLTDHF (T : LTDHF) : LPKE :=
  { kemPKE T.toTDHF with
    losCoins := T.losCoins
    losKeyGen := T.losKeyGen }

/-- Section C.2, p.50: the Section A.2 TDHF (`x = m ∥ r`, `Eval = Enc`, `hEval = m`,
`pInv = Dec`) on the recoverable part, with the lossy PKE's lossy key generator. -/
def ltdhfOfLPKE (l : ℕ → ℕ) (P : LPKE) : LTDHF :=
  { ofPKE l P.toPKE with
    losCoins := P.losCoins
    losKeyGen := P.losKeyGen }

end TrapdoorHCF.CCA2.Supplement


