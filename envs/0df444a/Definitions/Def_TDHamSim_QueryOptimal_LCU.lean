-- Prove2me | Definitions.Def_TDHamSim_QueryOptimal_LCU
-- name    : TDHamSim_QueryOptimal_LCU
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:21:54.131969+00:00
-- url     : https://prove2.me/theorems/f79d3793-a581-4f9d-8d9e-df04eaf01a98
-- title:
--   PREP, SELECT and normalization-two block encoding
-- statement:
--   The length and reuse registers each have $b=\lceil\log_2(4q+2)\rceil$ qubits. PREP places amplitude $\sqrt{|\lambda_N|/2}$ on a supported length and amplitude $\sqrt{(2-\Lambda)/2}$ on label $4q+1$. SELECT applies $\operatorname{sgn}(\lambda_N)V_N$ on a supported length; on the extra label it flips the public/private flag.
--
--   $$V=\mathrm{PREP}^{\dagger}\mathrm{SELECT}\,\mathrm{PREP}.$$
--
--   Both tensor-register and physical bit-register forms are given, with explicit zero auxiliary state. The subsequent amplification uses the already-defined sequence $-VR_WV^\dagger R_WV$. The extra label therefore contributes zero to the encoded block instead of silently changing its normalization.
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), (73)–(78), pp.29–30; (80), p.31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Resources

namespace TDHamSim.QueryOptimal

abbrev LCUIndex (b m a n : ℕ) := Fin (2^b) × (Fin (2^b) × Bits (1+m+a+n))
abbrev LCUAux (b m a : ℕ) := Fin (2^b) × (Fin (2^b) × Bits (1+m+a))
def auxZero (b m a : ℕ) : LCUAux b m a :=
  (⟨0, pow_pos (by decide) _⟩, ⟨0, pow_pos (by decide) _⟩, fun _ => false)
noncomputable def reusePhysical {m a n : ℕ} (b N : ℕ) (w : ℝ)
    (O : Fin (2^m) → Mat (Bits a × Bits n)) : Mat (Fin (2^b) × Bits (1+m+a+n)) :=
  fun x y => match decode m a n x.2, decode m a n y.2 with
    | some u, some v => reuseV b N w O (x.1, u) (y.1, v)
    | none, none => if x = y then 1 else 0
    | _, _ => 0

def inSupport (q N : ℕ) : Prop :=
  Even N ∧ ((2 ≤ N ∧ N ≤ 2*q-2) ∨ (2*q+2 ≤ N ∧ N ≤ 4*q))
noncomputable def coefficientPrep (q b : ℕ) : Mat (Fin (2^b)) := by
  classical
  exact realPrep ⟨0, pow_pos (by decide) _⟩ (fun x =>
    if inSupport q x.val then Real.sqrt (|lambda q x.val| / 2)
    else if x.val = 4*q+1 then Real.sqrt ((2-normalization q) / 2) else 0)
noncomputable def select {m a n : ℕ} (q b : ℕ) (w : ℝ)
    (O : Fin (2^m) → Mat (Bits a × Bits n)) : Mat (LCUIndex b m a n) := by
  classical
  exact fun x y => if x.1 = y.1 then
    if inSupport q x.1.val then
      (if lambda q x.1.val < 0 then -1 else 1) * reusePhysical b x.1.val w O x.2 y.2
    else if x.1.val = 4*q+1 then
      if x.2.1 = y.2.1 ∧
        x.2.2 = (fun i => if i.val = 0 then !(y.2.2 i) else y.2.2 i) then 1 else 0
    else if x.2 = y.2 then 1 else 0
  else 0
noncomputable def prepLCU (q b m a n : ℕ) : Mat (LCUIndex b m a n) :=
  fun x y => if x.2 = y.2 then coefficientPrep q b x.1 y.1 else 0
noncomputable def rawV {m a n : ℕ} (q b : ℕ) (w : ℝ)
    (O : Fin (2^m) → Mat (Bits a × Bits n)) : Mat (LCUIndex b m a n) :=
  (prepLCU q b m a n).conjTranspose * select q b w O * prepLCU q b m a n

def lcuCoords (b m a n : ℕ) (x : LCUAux b m a × Bits n) : LCUIndex b m a n :=
  (x.1.1, x.1.2.1, Fin.addCases x.1.2.2 x.2)
noncomputable def lcuV {m a n : ℕ} (q b : ℕ) (w : ℝ)
    (O : Fin (2^m) → Mat (Bits a × Bits n)) : Mat (LCUAux b m a × Bits n) :=
  fun x y => rawV q b w O (lcuCoords b m a n x) (lcuCoords b m a n y)
def lcuDecode (b m a n : ℕ) (x : Bits (2*b+(1+m+a+n))) : LCUIndex b m a n :=
  (timeIndex b (slice 0 b (by omega) x), timeIndex b (slice b b (by omega) x),
    slice (2*b) (1+m+a+n) (by omega) x)
noncomputable def selectBits {m a n : ℕ} (q b : ℕ) (w : ℝ)
    (O : Fin (2^m) → Mat (Bits a × Bits n)) : Mat (Bits (2*b+(1+m+a+n))) :=
  fun x y => select q b w O (lcuDecode b m a n x) (lcuDecode b m a n y)
noncomputable def vBits {m a n : ℕ} (q b : ℕ) (w : ℝ)
    (O : Fin (2^m) → Mat (Bits a × Bits n)) : Mat (Bits (2*b+(1+m+a+n))) :=
  fun x y => rawV q b w O (lcuDecode b m a n x) (lcuDecode b m a n y)

end TDHamSim.QueryOptimal


