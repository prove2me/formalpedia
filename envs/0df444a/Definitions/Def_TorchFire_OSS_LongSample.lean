-- Prove2me | Definitions.Def_TorchFire_OSS_LongSample
-- name    : TorchFire_OSS_LongSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:37:35.821206+00:00
-- url     : https://prove2.me/theorems/cebf4a69-5914-4c30-b6de-6a006c60f643
-- title:
--   The long-message OSS of Construction 4.13: $L$ instances, $\mathrm{Dig}$, $|A_a\rangle$, $U^O_{a,M}$, $\mathrm{OSS.Ver}$ (15)
-- statement:
--   **Construction 4.13** with $L=\lambda$: $L$ independent instances $O_c$ of Construction 4.7 and an independent uniformly random digest $\mathrm{Dig}:\mathcal M\to\{0,1\}^L$ (14), with public collection $O=(O_1,\dots,O_L,\mathrm{Dig})$. For a key $a=(a_1,\dots,a_L)$ and message $M$ with $\mathrm{Dig}(M)=(b_1,\dots,b_L)$ (15):
--
--   1. the signing state $|A_a\rangle=\bigotimes_c|W_{a_c}\rangle$;
--   2. the signing unitary $U^O_{a,M}=\bigotimes_cU^{O_c}_{a_c,b_c}$ and the signer's output on $\Sigma_1\cdots\Sigma_L$;
--   3. $\mathrm{OSS.Ver}^O(a,M,\sigma)=\prod_c\mathrm{OSS.Ver}^{O_c}(a_c,b_c,\sigma_c)$;
--   4. $\mathrm{OSS.GenQKey}^O$ (independent key generations, a cq-state on key × registers);
--   5. the anchor test effect $\bigotimes_c K_c^\dagger K_c$ of the coset test in every component.
--
--   The message space $\mathcal M$ is a parameter; strings of length at most $p$, $\{0,1\}^{\le p}$, are pairs of a length and a string.
--
--   **Formalization Note** (14) writes $\mathrm{Dig}:\{0,1\}^*\to\{0,1\}^L$, which has no uniform distribution; the message space is $\{0,1\}^{\le p(\lambda)}$ in Theorem 4.14 and $\{0,1\}^{\le1+\lambda+2Lr}$ in torch-fire (paper.md decision 10).
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Construction 4.13 (14)–(15) pp.22–23; Theorem 4.14 p.23; Construction 7.4 step 4 (i) p.53

import Mathlib
import Definitions.Def_TorchFire_OSS_signU
import Definitions.Def_TorchFire_OSS_prepCircuit
import Definitions.Def_TorchFire_OSS_Theta
import Definitions.Def_TorchFire_Model_thresholdEffect

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

/-- The message length `L = λ` of Construction 4.13 (p.22), at the effective parameter. -/
abbrev L (lam : ℕ) : ℕ := eff lam

/-- **Bit strings of length at most `p`**, `{0,1}^{≤p}` (Theorem 4.14, p.23): a length `m ≤ p` and a
string of that length. -/
abbrev BitStr (p : ℕ) : Type := Σ m : Fin (p + 1), Bits m

/-- **The oracle distribution of Construction 4.13** (Chatterjee–Mukherjee–Pathak–Podder, *Quantum
Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593, (i), p.22):
`L` independent one-bit instances `O_c` (Construction 4.7/4.2) and an independent uniformly random
digest `Dig : Msg → {0,1}^L` (14).

**Formalization Note** (14) writes `Dig : {0,1}* → {0,1}^L`, which carries no uniform distribution.
The message space `Msg` is a parameter: `{0,1}^{≤p(λ)}` for Theorem 4.14 and `{0,1}^{≤1+λ+2Lr}`
for torch-fire (paper.md decision 10). -/
abbrev LongSample (lam : ℕ) (Msg : Type) : Type :=
  (Fin (L lam) → OneSample lam) × (Msg → Bits (L lam))

variable {lam : ℕ} {Msg : Type}

/-- `Dig(M) = (b_1, …, b_L)`. -/
def dig (ω : LongSample lam Msg) (M : Msg) : Bits (L lam) := ω.2 M

/-- **The long-message signing state** `|A_a⟩ = ⨂_{c=1}^L |W_{a_c}⟩` (15), p.23, on the registers
`R_1 ⋯ R_L`. -/
noncomputable def longKeyState (ω : LongSample lam Msg) (a : Fin (L lam) → Bits (r lam)) :
    (Fin (L lam) → Bits (k lam)) → ℂ :=
  fun u => ∏ c, cosetState (ω.1 c) (a c) (u c)

/-- **The long-message signing unitary** `U^O_{a,M} = ⨂_{c=1}^L U^{O_c}_{a_c, b_c}` with
`Dig(M) = (b_1, …, b_L)` (15), p.23, on `(R_c E_c Σ_c)_{c ∈ [L]}`. -/
noncomputable def longSignU (ω : LongSample lam Msg) (a : Fin (L lam) → Bits (r lam)) (M : Msg) :
    Matrix (Fin (L lam) → SignSpace lam) (Fin (L lam) → SignSpace lam) ℂ :=
  piKron fun c => signU (ω.1 c) (a c) (dig ω M c)

/-- **`OSS.Ver^O(a, M, σ) = ∏_{c=1}^L OSS.Ver^{O_c}(a_c, b_c, σ_c)`** (Construction 4.13 (iv) and
(15), p.23). -/
def longVer (ω : LongSample lam Msg) (a : Fin (L lam) → Bits (r lam)) (M : Msg)
    (σ : Fin (L lam) → Sig lam) : Prop :=
  ∀ c, ver (ω.1 c) (a c) (dig ω M c) (σ c)

noncomputable instance (ω : LongSample lam Msg) (a : Fin (L lam) → Bits (r lam)) (M : Msg) :
    DecidablePred (longVer ω a M) := by
  intro σ; classical exact Classical.dec _

/-- The long signing input `ρ_R ⊗ |0⟩⟨0|` on `(R_c E_c Σ_c)_c`. -/
def longSignIn (ρ : Matrix (Fin (L lam) → Bits (k lam)) (Fin (L lam) → Bits (k lam)) ℂ) :
    Matrix (Fin (L lam) → SignSpace lam) (Fin (L lam) → SignSpace lam) ℂ :=
  Matrix.of fun s s' =>
    if (∀ c, (s c).2 = (0, none)) ∧ (∀ c, (s' c).2 = (0, none)) then
      ρ (fun c => (s c).1) (fun c => (s' c).1) else 0

/-- **The output of `OSS.Sign^O(a, ρ_R, M)`** (Construction 4.13 (iii), p.23): the state of
`(Σ_c)_c` after `U^O_{a,M}`. -/
noncomputable def longSignOut (ω : LongSample lam Msg) (a : Fin (L lam) → Bits (r lam)) (M : Msg)
    (ρ : Matrix (Fin (L lam) → Bits (k lam)) (Fin (L lam) → Bits (k lam)) ℂ) :
    Matrix (Fin (L lam) → Sig lam) (Fin (L lam) → Sig lam) ℂ :=
  traceOutVia
    (fun p : (Fin (L lam) → Sig lam) × (Fin (L lam) → Bits (k lam) × SignWs lam) =>
      fun c => ((p.2 c).1, (p.2 c).2, p.1 c))
    (conjMat (longSignU ω a M) (longSignIn ρ))

/-- **`OSS.GenQKey^O`** of Construction 4.13 (ii), p.23: independent one-bit key generations in the
`L` components, as a cq-state on (key `a`) × (`R_1 ⋯ R_L`). -/
noncomputable def longGenQKeyCQ (ω : LongSample lam Msg) :
    Matrix ((Fin (L lam) → Bits (r lam)) × (Fin (L lam) → Bits (k lam)))
      ((Fin (L lam) → Bits (r lam)) × (Fin (L lam) → Bits (k lam))) ℂ :=
  Matrix.of fun p p' => ∏ c, genQKeyCQ (ω.1 c) (p.1 c, p.2 c) (p'.1 c, p'.2 c)

/-- The query domain of the long-message public collection `O = (O_1, …, O_L, Dig)` (p.22). -/
abbrev LongDom (lam : ℕ) (Msg : Type) : Type := (Fin (L lam) × PubDom lam) ⊕ Msg

/-- Its answer register. -/
abbrev LongAns (lam : ℕ) : Type := PubAns lam × Bits (L lam)

instance (lam : ℕ) (Msg : Type) [Fintype Msg] : Fintype (LongDom lam Msg) := inferInstance
instance (lam : ℕ) (Msg : Type) [DecidableEq Msg] : DecidableEq (LongDom lam Msg) :=
  inferInstance
instance (lam : ℕ) : Fintype (LongAns lam) := inferInstance
instance (lam : ℕ) : DecidableEq (LongAns lam) := inferInstance
noncomputable instance (lam : ℕ) (Msg : Type) [Fintype Msg] [DecidableEq Msg] :
    Fintype (LongSample lam Msg) := inferInstance

/-- **The long-message public collection** `O = (O_1, …, O_L, Dig)` of Construction 4.13 (i), p.22,
as one combined oracle (paper.md decision 3). -/
noncomputable def longPubOracle (ω : LongSample lam Msg) : LongDom lam Msg → LongAns lam :=
  combine (indexed fun c => pubOracle (ω.1 c)) (dig ω)

/-- **The anchor test of a long-message key** (Construction 7.4 step 4 (i), p.53): the coset test of
Remark 4.9 in every component; its accepting effect `⨂_c K_cᴴ K_c`. -/
noncomputable def longTestEffect (ω : LongSample lam Msg) (a : Fin (L lam) → Bits (r lam)) :
    Matrix (Fin (L lam) → Bits (k lam)) (Fin (L lam) → Bits (k lam)) ℂ :=
  piKron fun c => (cosetTestKraus (ω.1 c) (a c))ᴴ * cosetTestKraus (ω.1 c) (a c)

end TorchFire.OSS


