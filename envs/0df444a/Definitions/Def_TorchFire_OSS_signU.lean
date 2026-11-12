-- Prove2me | Definitions.Def_TorchFire_OSS_signU
-- name    : TorchFire_OSS_signU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:35:28.085652+00:00
-- url     : https://prove2.me/theorems/a9ee510e-f3c3-4890-b991-338322cda378
-- title:
--   The repeated-trial signer of Construction 4.7, its coherent unitary $U^O_{y,b}$, $\mathrm{OSS.Ver}$ (9) and $\epsilon_{y,b}$
-- statement:
--   **Construction 4.7 (iii)** (the repeated-trial signer of [ÇGS26, §6.2]): for $j=1,\dots,\lambda$, measure the first qubit of $R$, obtaining $c$; if $c=b$, measure the remaining qubits and return $u=b\Vert u'$; otherwise apply $H^{\otimes k}$, evaluate $D(y,\cdot)$ into a fresh qubit, measure it, apply $H^{\otimes k}$ and continue; return $\perp$ after $\lambda$ failures.
--
--   The module gives the **coherent signing unitary $U^O_{y,b}$** on $R\,E\,\Sigma$ (Remark 4.12): each measurement is a coherent copy into a record register $E$, each classically controlled step a controlled gate, and the signature is copied into $\Sigma$, whose zero state is $|\perp\rangle$ (Fact 3.1). It also defines the signer's output state on $\Sigma$ (whose diagonal is the signature distribution (13)), **$\mathrm{OSS.Ver}^O(y,b,u)=1[P^{-1}(y,u)\ne\perp]\wedge1[u_1=b]$** (9), the pointwise signing error
--   $$\epsilon_{y,b}=\Pr[\mathrm{OSS.Ver}^O(y,b,u)=0:\ u\leftarrow\mathrm{OSS.Sign}^O(y,|W_y\rangle\langle W_y|,b)]$$
--   of Theorem 4.10, and $\hat U^O_b=\sum_y|y\rangle\langle y|_Y\otimes U^O_{y,b}$ (App. A.1), the signer controlled on an unmeasured key register.
--
--   **Formalization Note** Remark 4.12 obtains $U^O_{y,b}$ from the signer by Fact 3.1; here the deferred-measurement circuit is written out gate by gate, and the signature distribution is read from it as in (13).
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Construction 4.7 (iii)–(iv), (9) p.21; Remark 4.12 (13) p.22; Theorem 4.10 p.22; App. A.1 p.80

import Mathlib
import Definitions.Def_TorchFire_OSS_OneSample
import Definitions.Def_TorchFire_Model_traceDist

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

variable {lam : ℕ}

lemma k_pos (lam : ℕ) : 0 < k lam :=
  Nat.lt_of_lt_of_le (Nat.mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_right lam 2)))
    (Nat.le_add_left _ _)

/-- The first qubit `u_1` of a `k`-bit string. -/
def firstBit (u : Bits (k lam)) : ZMod 2 := u ⟨0, k_pos lam⟩

/-- **The measurement records of the signer**: for each of the `λ` trials, the measured first
qubit `c_j`, a success flag `s_j`, and the measured `D`-qubit `B_j` (Construction 4.7 (iii),
p.21). -/
abbrev SignWs (lam : ℕ) : Type := Fin (eff lam) → ZMod 2 × ZMod 2 × ZMod 2

/-- **The signature register `Σ`**: a `k`-bit signature or the failure state `|⊥⟩_Σ` (Remark 4.12,
p.22: "The basis state `|⊥⟩_Σ` denotes failure"). `none` is `⊥` and is the register's initial
zero state. -/
abbrev Sig (lam : ℕ) : Type := Option (Bits (k lam))

/-- The registers `R E Σ` of the coherent signer (Remark 4.12, p.22). -/
abbrev SignSpace (lam : ℕ) : Type := Bits (k lam) × SignWs lam × Sig lam

instance (lam : ℕ) : Fintype (SignWs lam) := inferInstance
instance (lam : ℕ) : DecidableEq (SignWs lam) := inferInstance
instance (lam : ℕ) : Fintype (Sig lam) := inferInstance
instance (lam : ℕ) : DecidableEq (Sig lam) := inferInstance
instance (lam : ℕ) : Fintype (SignSpace lam) := inferInstance
instance (lam : ℕ) : DecidableEq (SignSpace lam) := inferInstance

/-- No earlier trial has succeeded. -/
def notDone (j : Fin (eff lam)) (s : SignSpace lam) : Prop :=
  ∀ j' : Fin (eff lam), j'.val < j.val → (s.2.1 j').2.1 = 0

noncomputable instance (j : Fin (eff lam)) : DecidablePred (notDone (lam := lam) j) := by
  intro s; unfold notDone; infer_instance

/-- Replace the record of trial `j`. -/
def setRec (s : SignSpace lam) (j : Fin (eff lam)) (v : ZMod 2 × ZMod 2 × ZMod 2) :
    SignSpace lam :=
  (s.1, Function.update s.2.1 j v, s.2.2)

/-- **One trial of `OSS.Sign^O(y, R, b)`**, coherently (Construction 4.7 (iii)(a)–(b), p.21, in the
deferred-measurement form of Fact 3.1, p.18), acting only if no earlier trial succeeded:

1. measure the first qubit of `R` (copy it into `c_j`);
2. success iff `c_j = b` (flag `s_j`); on success measure the remaining qubits, i.e. copy `R` into
   `Σ` (`u = b ∥ u′`, which is the content of `R`);
3. on failure apply `H^{⊗k}` to `R`, evaluate `D(y, ·)` into the fresh qubit `B_j` (measured, i.e.
   kept as a record), and apply `H^{⊗k}` to `R`. -/
noncomputable def trial (ω : OneSample lam) (y : Bits (r lam)) (b : ZMod 2) (j : Fin (eff lam)) :
    Matrix (SignSpace lam) (SignSpace lam) ℂ :=
  by classical exact
  let fail : SignSpace lam → Prop := fun s => notDone j s ∧ (s.2.1 j).2.1 = 0
  let g1 := basisMat fun s : SignSpace lam =>
    setRec s j ((s.2.1 j).1 + (if notDone j s then firstBit s.1 else 0), (s.2.1 j).2)
  let g2 := basisMat fun s : SignSpace lam =>
    setRec s j ((s.2.1 j).1,
      (s.2.1 j).2.1 + (if notDone j s ∧ (s.2.1 j).1 = b then 1 else 0), (s.2.1 j).2.2)
  let g3 := basisMat fun s : SignSpace lam =>
    (s.1, s.2.1, if (s.2.1 j).2.1 = 1 then Equiv.swap none (some s.1) s.2.2 else s.2.2)
  let gH := ctrlOn fail (hadOn fun s : SignSpace lam => (s.1, s.2))
  let g5 := basisMat fun s : SignSpace lam =>
    setRec s j ((s.2.1 j).1, (s.2.1 j).2.1,
      (s.2.1 j).2.2 + (if fail s then D ω (y, s.1) else 0))
  gH * g5 * gH * g3 * g2 * g1

/-- **The coherent signing unitary `U^O_{y,b}`** on `R E Σ` (Remark 4.12, p.22): the `λ` trials of
Construction 4.7 (iii) in order, `U = Trial_λ ⋯ Trial_1`, obtained from `OSS.Sign^O(y, ·, b)` by
Fact 3.1. If every trial fails, `Σ` stays `|⊥⟩`. -/
noncomputable def signU (ω : OneSample lam) (y : Bits (r lam)) (b : ZMod 2) :
    Matrix (SignSpace lam) (SignSpace lam) ℂ :=
  ((List.finRange (eff lam)).map (trial ω y b)).reverse.prod

/-- The signing input `ρ_R ⊗ |0⟩⟨0|_{EΣ}` (all records `0`, `Σ = |⊥⟩`). -/
def signIn (ρ : Matrix (Bits (k lam)) (Bits (k lam)) ℂ) :
    Matrix (SignSpace lam) (SignSpace lam) ℂ :=
  Matrix.of fun s s' => if s.2 = (0, none) ∧ s'.2 = (0, none) then ρ s.1 s'.1 else 0

/-- **The output of `OSS.Sign^O(y, ρ_R, b)`**: the state of `Σ` after `U^O_{y,b}`; its diagonal is
the signature distribution (13), p.22. -/
noncomputable def signOut (ω : OneSample lam) (y : Bits (r lam)) (b : ZMod 2)
    (ρ : Matrix (Bits (k lam)) (Bits (k lam)) ℂ) : Matrix (Sig lam) (Sig lam) ℂ :=
  traceOutVia (fun p : Sig lam × (Bits (k lam) × SignWs lam) => (p.2.1, p.2.2, p.1))
    (conjMat (signU ω y b) (signIn ρ))

/-- **`OSS.Ver^O(y, b, u) = 1[P⁻¹(y, u) ≠ ⊥] ∧ 1[u_1 = b]`** (9), p.21, for a `k`-bit `u`. -/
def verBits (ω : OneSample lam) (y : Bits (r lam)) (b : ZMod 2) (u : Bits (k lam)) : Prop :=
  (Pinv ω (y, u)).isSome ∧ firstBit u = b

/-- `OSS.Ver` on the signer's output register: `⊥` is rejected. -/
def ver (ω : OneSample lam) (y : Bits (r lam)) (b : ZMod 2) : Sig lam → Prop
  | none => False
  | some u => verBits ω y b u

noncomputable instance (ω : OneSample lam) (y : Bits (r lam)) (b : ZMod 2) :
    DecidablePred (ver ω y b) := by
  intro σ; classical exact Classical.dec _

/-- **The pointwise signing error** `ϵ_{y,b} = Pr[OSS.Ver^O(y, b, u) = 0 : u ← OSS.Sign^O(y,
|W_y⟩⟨W_y|, b)]` (Theorem 4.10, p.22). -/
noncomputable def signErr (ω : OneSample lam) (y : Bits (r lam)) (b : ZMod 2) : ℝ :=
  ∑ σ : Sig lam, if ver ω y b σ then 0 else
    (signOut ω y b (ketbra (cosetState ω y)) σ σ).re

/-- **`Û^O_b = Σ_y |y⟩⟨y|_Y ⊗ U^O_{y,b}`** (App. A.1, p.80): the signing circuit controlled on a
verification-key register `Y` that is not measured. -/
noncomputable def signUY (ω : OneSample lam) (b : ZMod 2) :
    Matrix (Bits (r lam) × SignSpace lam) (Bits (r lam) × SignSpace lam) ℂ :=
  Matrix.of fun p p' => if p.1 = p'.1 then signU ω p.1 b p.2 p'.2 else 0

end TorchFire.OSS


