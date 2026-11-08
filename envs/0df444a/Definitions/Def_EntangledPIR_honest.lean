-- Prove2me | Definitions.Def_EntangledPIR_honest
-- name    : EntangledPIR_honest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:30.924103+00:00
-- url     : https://prove2.me/theorems/a0306b1a-06b5-40cf-89bb-7619381f9ad0
-- title:
--   The honest servers A and B of Protocol 1 and the Bell pairs
-- statement:
--   The honest servers hold the registers of all copies $(i,j)\in[k]\times[4]$, and a register $\mathsf R_0$ that they leave untouched. The shared resource is the product of $|\Phi^+\rangle^{\otimes(d+m2^d)}$ over the copies, $4k(d+m2^d)$ Bell pairs, and it does not depend on the database.
--
--   Honest A: in round 0, for every copy $(i,j)$ it applies $U_{F_i}X^{a_{i,j}}_{\mathsf P}$ and measures $\mathsf P$ in the Hadamard basis, and sends all $e_{i,j}$ (step 2). In round 3, for every $i$ it measures $\mathsf Y_{K_i}$ of copy $(i,t_i)$ and sends $u=u_1\oplus\dots\oplus u_k$ (step 5(b)).
--
--   Honest B: in round 1, for every trap $(i,j)$, $j\ne t_i$, it tests the copy with mask $b_{i,j}$ and table $F_i$ by the Lüders map of $\Pi^{b_{i,j}}_f$, and sends the outcomes (step 3(b)). In round 2, on acceptance, for every $i$ it measures $\mathsf P'$ of copy $(i,t_i)$, obtaining $J_i$, sets $K_i=J_i\oplus b_{i,t_i}$, measures $\mathsf Y'_{K_i}$, obtaining $v_i$, and sends $K$ and $v=v_1\oplus\dots\oplus v_k$ (step 4).
--
--   In all other rounds and on every other message they are idle.
--
--   **Formalization Note** For every initial state the honest server applies its prescribed instrument to its part of that state (A.1). Each server is a `Strategy`, so the honest ones and the malicious ones are in one model.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Protocol 1, p.26; §5.2, p.25; A.1, p.53

import Definitions.Def_EntangledPIR_tensorInstr
import Definitions.Def_EntangledPIR_copyComplete
import Definitions.Def_EntangledPIR_clientStep

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Protocol 1,
p.26: the honest servers A and B, and the Bell pairs.
-/

open Matrix
open scoped Kronecker

namespace EntangledPIR

/-- The registers that an honest server holds for the copies of Protocol 1: one `CopyReg` for every
copy `(i, j) ∈ [k] × [4]`, p.26. -/
abbrev Copies (n m lam : ℕ) : Type :=
  CopyIdx (shareCount n lam) → CopyReg (queryLen n lam) m

instance (n m lam : ℕ) : DecidableEq (Copies n m lam) :=
  fun a b => Fintype.decidablePiFintype a b

/-- The Bell pairs of Protocol 1, indexed by copy and qubit, p.26. The text says "in total
`4k(d + m 2^d)` Bell pairs", and this index type has that many elements (the verification file proves
it). -/
abbrev BellIdx (n m lam : ℕ) : Type :=
  CopyIdx (shareCount n lam) × CopyQubit (queryLen n lam) m

/-- The state of the Bell pairs of Protocol 1, p.26: the product over the copies of
`|Φ+⟩^{⊗(d + m 2^d)}`. The database does not occur in it. -/
noncomputable def bellVector (n m lam : ℕ) : Copies n m lam × Copies n m lam → ℂ :=
  fun p => ∏ c, bellCopy (queryLen n lam) m (p.1 c, p.2 c)

/-- A completeness relation with a trivial outcome on the copies that an operation does not touch. -/
theorem sel_complete {ι V X : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
    (sel : ι → Prop) [DecidablePred sel] (Mon : ι → V → Matrix X X ℂ) (v0 : V)
    (h : ∀ c, sel c → ∑ v, (Mon c v)ᴴ * Mon c v = 1) (c : ι) :
    ∑ v, (if sel c then Mon c v else if v = v0 then 1 else 0)ᴴ *
      (if sel c then Mon c v else if v = v0 then 1 else 0) = 1 := by
  by_cases hc : sel c
  · simp only [if_pos hc]; exact h c hc
  · simp only [if_neg hc]; exact trivial_complete v0

section
variable {n m : ℕ} (lam : ℕ) (F : Bits n → Bits m) (R0 : Type) [Fintype R0] [DecidableEq R0]

/-- The instrument of step 2 of Protocol 1, p.26: for every copy `(i, j)`, server A applies
`U_{F_i} X^{a_{i,j}}_P` to its registers of the copy and measures `P` in the Hadamard basis, obtaining
`e_{i,j}`; it sends all outcomes. It acts on each copy separately, and never touches `R0`. -/
noncomputable def stepTwoA (a : CopyIdx (shareCount n lam) → Bits (queryLen n lam)) :
    Instrument (Copies n m lam × R0) (Copies n m lam × R0) (BitStr (msgBound n m lam)) :=
  tensorInstr
    (fun (c : CopyIdx (shareCount n lam)) (e : Bits (queryLen n lam)) =>
      opKraus (table lam F c.1) (a c) e)
    (fun _ => opKraus_complete _ _)
    (fun κ => BitStr.ofList _ (serMat κ))

/-- The instrument of step 5(b) of Protocol 1, p.26: for every `i`, server A measures `Y_{K_i}` of copy
`(i, t_i)` in the computational basis, obtaining `u_i`, and sends `u = u_1 ⊕ ⋯ ⊕ u_k`. -/
noncomputable def stepFiveA (t : Fin (shareCount n lam) → Fin 4)
    (K : Fin (shareCount n lam) → Bits (queryLen n lam)) :
    Instrument (Copies n m lam × R0) (Copies n m lam × R0) (BitStr (msgBound n m lam)) :=
  tensorInstr
    (fun (c : CopyIdx (shareCount n lam)) (u : Bits m) =>
      if c.2 = t c.1 then outProj (K c.1) u else if u = bzero m then 1 else 0)
    (sel_complete _ _ _ fun _ _ => outProj_complete _)
    (fun κ => BitStr.ofList _ (List.ofFn (bigXor Finset.univ fun i => κ (i, t i))))

/-- The instrument of step 3(b) of Protocol 1, p.26: for every trap `(i, j)`, `j ≠ t_i`, server B tests
the copy with mask `b_{i,j}` and table `F_i`, by the Lüders map of `Π^{b_{i,j}}_f`, p.21, and sends the
test outcomes `f_{i,j}`. -/
noncomputable def stepThreeB (b : CopyIdx (shareCount n lam) → Bits (queryLen n lam))
    (t : Fin (shareCount n lam) → Fin 4) :
    Instrument (Copies n m lam × R0) (Copies n m lam × R0) (BitStr (msgBound n m lam)) :=
  tensorInstr
    (fun (c : CopyIdx (shareCount n lam)) (f : Bits (queryLen n lam)) =>
      if c.2 ≠ t c.1 then testProj (table lam F c.1) (b c) f
      else if f = bzero _ then 1 else 0)
    (sel_complete _ _ _ fun _ _ => testProj_complete _ _)
    (fun κ => BitStr.ofList _ (serTraps t κ))

/-- The instrument of step 4 of Protocol 1, p.26: for every `i`, server B measures `P′` of copy
`(i, t_i)` in the computational basis, obtaining `J_i`, computes `K_i = J_i ⊕ b_{i,t_i}`, measures
`Y′_{K_i}`, obtaining `v_i`, and sends `K` and `v = v_1 ⊕ ⋯ ⊕ v_k`. -/
noncomputable def stepFourB (b : CopyIdx (shareCount n lam) → Bits (queryLen n lam))
    (t : Fin (shareCount n lam) → Fin 4) :
    Instrument (Copies n m lam × R0) (Copies n m lam × R0) (BitStr (msgBound n m lam)) :=
  tensorInstr
    (fun (c : CopyIdx (shareCount n lam)) (o : Bits (queryLen n lam) × Bits m) =>
      if c.2 = t c.1 then computeKraus (b c) o.1 o.2
      else if o = (bzero _, bzero m) then 1 else 0)
    (sel_complete _ _ _ fun _ _ => computeKraus_complete _)
    (fun κ => BitStr.ofList _
      (serVec (fun i => bxor (κ (i, t i)).1 (b (i, t i))) ++
        List.ofFn (bigXor Finset.univ fun i => (κ (i, t i)).2)))

/-- The instrument of the honest A in round `r`, given the client's current message, p.26: step 2 in
round 0, step 5(b) in round 3. In every other round, and on every other message (the abort message
in particular), it is idle. -/
noncomputable def honestAInstr (r : ℕ) (cur : List Bool) :
    Instrument (Copies n m lam × R0) (Copies n m lam × R0) (BitStr (msgBound n m lam)) :=
  let k := shareCount n lam
  let d := queryLen n lam
  match r with
  | 0 =>
    if cur.length = 4 * k * d then stepTwoA lam F R0 (parseMat k d cur) else idleInstr _
  | 3 =>
    if cur.length = 2 * k + k * d then
      stepFiveA lam R0 (parsePos k cur) (parseVec k d cur (2 * k))
    else idleInstr _
  | _ => idleInstr _

/-- The instrument of the honest B in round `r`, given its classical history and the client's current
message, p.26: idle in round 0, in which it receives its masks; step 3(b) in round 1, on receiving `t`;
step 4 in round 2, on receiving the decision "accept". Otherwise it is idle. -/
noncomputable def honestBInstr (r : ℕ) (h : ServerHistory) (cur : List Bool) :
    Instrument (Copies n m lam × R0) (Copies n m lam × R0) (BitStr (msgBound n m lam)) :=
  let k := shareCount n lam
  let d := queryLen n lam
  let masks := parseMat k d (h.headD ([], [])).1
  match r with
  | 1 =>
    if cur.length = 2 * k then stepThreeB lam F R0 masks (parsePos k cur) else idleInstr _
  | 2 =>
    if cur = acceptMsg then stepFourB lam R0 masks (parsePos k (h.getD 1 ([], [])).1)
    else idleInstr _
  | _ => idleInstr _

/-- **The honest server A**, p.26, as a strategy: it holds the copies and a register `R0` that it leaves
untouched. For every initial state an honest server applies its prescribed instrument to its part of
that state (A.1, p.53). -/
noncomputable def honestA : Strategy (msgBound n m lam) where
  Reg := fun _ => Copies n m lam × R0
  fin := fun _ => inferInstance
  dec := fun _ => inferInstance
  instr := fun r _ cur => honestAInstr lam F R0 r cur

/-- **The honest server B**, p.26, as a strategy. -/
noncomputable def honestB : Strategy (msgBound n m lam) where
  Reg := fun _ => Copies n m lam × R0
  fin := fun _ => inferInstance
  dec := fun _ => inferInstance
  instr := fun r h cur => honestBInstr lam F R0 r h cur

end

end EntangledPIR


