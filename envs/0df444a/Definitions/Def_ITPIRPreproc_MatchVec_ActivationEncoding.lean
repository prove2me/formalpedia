-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_ActivationEncoding
-- name    : ITPIRPreproc_MatchVec_ActivationEncoding
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:15.768772+00:00
-- url     : https://prove2.me/theorems/4466a26b-a585-4a5c-92cf-fccc097deb18
-- title:
--   Appendix A — fixed-width codes and program bundle for the activation-bit primitive
-- statement:
--   Fix the concrete bit representations used by the activation-bit matching-vector implementation. A Boolean matrix is encoded in row-major order and followed by the activation vector; a vector over $\mathbb F_3$ is encoded by two bits per coordinate; the secret is one bit. On non-power-of-two sizes, where `actFamily` uses its placeholder primitive, the codes are empty. On real sizes the public table is `mvTableCode`. The module also defines the seven-program bundle and assembles it with these codes into an `OCHPImpl`. Explicit projection lemmas handle the dependent size cast in `actFamily`.
-- source:
--   Claim 6.2.4(i), printed p.23 (PDF p.25): the encoding is any fixed injective polynomial-time code; Appendix A, printed pp.38–39 (PDF pp.40–41). The concrete layouts here instantiate that freedom for keys (14), hints and answers (16)–(17), printed pp.20–21.

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive
import Definitions.Def_ITPIRPreproc_MatchVec_OfflineEfficiency

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-- Projections through the size cast used by `actFamily`. -/
lemma castOCHPKey {k m : ℕ} (hm : k = m) (P : OCHP (k * k)) :
    (cast (congrArg (fun t => OCHP (t * t)) hm) P).Key = P.Key := by
  subst m; rfl

lemma castOCHPHintVal {k m : ℕ} (hm : k = m) (P : OCHP (k * k)) :
    (cast (congrArg (fun t => OCHP (t * t)) hm) P).HintVal = P.HintVal := by
  subst m; rfl

lemma castOCHPSecret {k m : ℕ} (hm : k = m) (P : OCHP (k * k)) :
    (cast (congrArg (fun t => OCHP (t * t)) hm) P).Secret = P.Secret := by
  subst m; rfl

lemma castOCHPAnsVal {k m : ℕ} (hm : k = m) (P : OCHP (k * k)) :
    (cast (congrArg (fun t => OCHP (t * t)) hm) P).AnsVal = P.AnsVal := by
  subst m; rfl

/-- At a power-of-two size the placeholder branch of `actFamily` is not taken. -/
lemma actFamily_pow_two (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (h : ℕ) :
    actFamily dim u v (2 ^ h) = actPrimitive (dim h) (u h) (v h) := by
  have hh : Nat.log 2 (2 ^ h) = h := Nat.log_pow (by omega) h
  have hp : HEq (actPrimitive (dim (Nat.log 2 (2 ^ h))) (u (Nat.log 2 (2 ^ h)))
      (v (Nat.log 2 (2 ^ h)))) (actPrimitive (dim h) (u h) (v h)) := by
    congr
  have hm : 2 ^ Nat.log 2 (2 ^ h) = 2 ^ h := by rw [Nat.log_pow (by omega)]
  unfold actFamily
  rw [dif_pos hm]
  exact eq_of_heq ((cast_heq _ _).trans hp)

/-- One bit for an element of `F₂`. -/
def encF2 (x : ZMod 2) : List Bool := [decide (x = 1)]

/-- Fixed-width code of a vector over `F₂`. -/
def encF2Vec {d : ℕ} (x : Fin d → ZMod 2) : List Bool :=
  List.ofFn fun k => decide (x k = 1)

/-- Fixed-width `(h+1)d`-bit code of an activation key: the matrix in row-major order,
followed by the activation vector. -/
def encActKeyRaw {h d : ℕ} (K : ActKey h d) : List Bool :=
  (List.ofFn fun r : Fin h => List.ofFn fun k : Fin d => decide (K.1 r k = 1)).flatten ++
    encF2Vec K.2

/-- Two bits per coordinate for a vector over `F₃` (`0 ↦ 00`, `1 ↦ 10`, `2 ↦ 01`,
where the list is least-significant bit first). -/
def encF3Vec {d : ℕ} (z : Fin d → ZMod 3) : List Bool :=
  (List.ofFn fun k : Fin d => natBits 2 (z k).val).flatten

/-- The public matching-vector table at sizes for which the activation primitive is defined. -/
noncomputable def actTable (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ) : List Bool :=
  if _hm : 2 ^ Nat.log 2 m = m then mvTableCode (u (Nat.log 2 m)) (v (Nat.log 2 m)) else []

/-- Fixed-width key code, with the empty code on the placeholder branch. -/
noncomputable def actEncKey (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ)
    (K : (actFamily dim u v m).Key) : List Bool :=
  if hm : 2 ^ Nat.log 2 m = m then
    encActKeyRaw (h := Nat.log 2 m) (d := dim (Nat.log 2 m)) (cast (by
      unfold actFamily
      rw [dif_pos hm]
      exact castOCHPKey hm _) K)
  else []

/-- Two-bit-per-coordinate hint code, with the empty code on the placeholder branch. -/
noncomputable def actEncHint (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ)
    (z : (actFamily dim u v m).HintVal) : List Bool :=
  if hm : 2 ^ Nat.log 2 m = m then
    encF3Vec (d := dim (Nat.log 2 m)) (cast (by
      unfold actFamily
      rw [dif_pos hm]
      exact castOCHPHintVal hm _) z)
  else []

/-- One-bit secret code, with the empty code on the placeholder branch. -/
noncomputable def actEncSecret (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ)
    (s : (actFamily dim u v m).Secret) : List Bool :=
  if hm : 2 ^ Nat.log 2 m = m then
    encF2 (cast (by
      unfold actFamily
      rw [dif_pos hm]
      exact castOCHPSecret hm _) s)
  else []

/-- Two-bit-per-coordinate answer code, with the empty code on the placeholder branch. -/
noncomputable def actEncAns (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ)
    (a : (actFamily dim u v m).AnsVal) : List Bool :=
  if hm : 2 ^ Nat.log 2 m = m then
    encF3Vec (d := dim (Nat.log 2 m)) (cast (by
      unfold actFamily
      rw [dif_pos hm]
      exact castOCHPAnsVal hm _) a)
  else []

/-- Bundle the programs of the non-streaming activation implementation. -/
structure ActPrograms where
  table : Program
  sampleKey : Program
  sampleCompat : Program
  testCompat : Program
  query : Program
  answer : Program
  decode : Program

/-- Assemble the activation implementation from its codes, public table and programs. -/
noncomputable def actImpl (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
    (p : ActPrograms) : OCHPImpl (actFamily dim u v) where
  encKey := actEncKey dim u v
  encHint := actEncHint dim u v
  encSecret := actEncSecret dim u v
  encAns := actEncAns dim u v
  table := actTable dim u v
  tableProg := p.table
  sampleKey := p.sampleKey
  sampleCompat := p.sampleCompat
  testCompat := p.testCompat
  query := p.query
  answer := p.answer
  decode := p.decode
  streamInit := [Instr.halt]
  streamChunk := [Instr.halt]

end ITPIRPreproc.MatchVec


