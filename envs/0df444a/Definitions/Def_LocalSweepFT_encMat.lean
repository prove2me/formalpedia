-- Prove2me | Definitions.Def_LocalSweepFT_encMat
-- name    : LocalSweepFT_encMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:42:09.986261+00:00
-- url     : https://prove2.me/theorems/700051c8-ae53-4f38-a102-dfcbe9e905f7
-- title:
--   Registers of the $(d,d')$-Toric code, its code space, and the nice encoding $|\bar a\rangle$
-- statement:
--   A register of the side-$n$ $(d,d')$-Toric code has one qubit per $d'$-cell of $\mathcal T^d_n$; a basis string is read as a $d'$-chain. With $C_Z^\perp=\operatorname{im}\partial^-$ (the X-stabilizers) and $|A\rangle=|A|^{-1/2}\sum_{a\in A}|a\rangle$, the **nice encoding** with direction set $S'$ is
--   $$|\bar0\rangle=|C_Z^\perp\rangle,\qquad|\bar1\rangle=|x_{S'}+C_Z^\perp\rangle,$$
--   and $\mathrm{Enc}:|a\rangle\mapsto|\bar a\rangle$ is the encoding isometry. The code space of the $(d,i)$-Toric code is the span of the coset states $|c+C_Z^\perp\rangle$ of the $i$-cycles $c$.
--
--   Every quantum register of a Toric encoded circuit is in this encoding.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definition 4.3, p.17; CSS codes, p.12; Definition 4.36, p.35

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_xLog

open Matrix

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…): the qubits of one register of the `(d, d′)`-Toric code
(Def 4.3, p.17), its code space, and the nice encoding (Def 4.36, p.35). -/

/-- The physical qubits of one register of the side-`n` `(d, i)`-Toric code: the `i`-cells of
`T^d_n` (Def 4.3, p.17). A computational-basis state is a function `QCell d i n → 𝔽₂`. -/
abbrev QCell (d i n : ℕ) := Cell (ZMod n) d i

variable {d d' n : ℕ} [NeZero n]

/-- A computational-basis string of a register, read as a chain (Def 4.2, p.16: `C_i` is
identified with `𝔽₂^{F_i}`). -/
noncomputable def toChain {i : ℕ} (y : QCell d i n → ZMod 2) : Chain (ZMod n) d i :=
  Finsupp.equivFunOnFinite.symm y

open Classical in
/-- The amplitude of the basis string `y` in the logical state `|ā⟩` of the nice encoding
(Def 4.36, p.35): `|0̄⟩ = |C_Z^⊥⟩`, `|1̄⟩ = |x_{S′} + C_Z^⊥⟩`, where `C_Z^⊥ = im ∂⁻` (the
X-stabilizers, p.39) and `|A⟩ := |A|^{−1/2} Σ_{a∈A} |a⟩` (p.12). -/
noncomputable def encAmp (S : DirSet d d') (a : ZMod 2) (y : QCell d d' n → ZMod 2) : ℂ :=
  if toChain y - a • xLog S ∈ bdryRange (ZMod n) d d' then
    ((Real.sqrt (Nat.card (bdryRange (ZMod n) d d')) : ℂ))⁻¹ else 0

/-- The encoding isometry `Enc : ℂ² → register`, `|a⟩ ↦ |ā⟩`, of the nice encoding with direction
set `S′` (Def 4.36, p.35). -/
noncomputable def encMat (S : DirSet d d') : Matrix (QCell d d' n → ZMod 2) (Fin 1 → ZMod 2) ℂ :=
  fun y a => encAmp S (a 0) y

open Classical in
/-- The (unnormalized) coset state `Σ_{s ∈ im ∂⁻} |c + s⟩` of an `i`-chain `c`. -/
noncomputable def cosetVec {i : ℕ} (c : Chain (ZMod n) d i) : (QCell d i n → ZMod 2) → ℂ :=
  fun y => if toChain y - c ∈ bdryRange (ZMod n) d i then 1 else 0

/-- The code space of the side-`n` `(d, i)`-Toric code: the span of the coset states `|c + C_Z^⊥⟩`
of the `i`-cycles `c ∈ C_X = ker ∂⁻` (p.12, "CSS codes"). -/
noncomputable def codeSpace (d i n : ℕ) [NeZero n] :
    Submodule ℂ ((QCell d i n → ZMod 2) → ℂ) :=
  Submodule.span ℂ {ψ | ∃ c : Chain (ZMod n) d i, bdry c = 0 ∧ ψ = cosetVec c}

end LocalSweepFT


