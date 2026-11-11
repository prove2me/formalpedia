-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_boolPhaseGate
-- name    : UnitaryQIPPSPACE_boolPhaseGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:59.541207+00:00
-- url     : https://prove2.me/theorems/ff1e6017-54ec-45f9-8925-f36688b9fc53
-- title:
--   Boolean phase gates and states, $O_f$, iterated differences (Definition 4.9)
-- statement:
--   For $g:\{0,1\}^m\to\{0,1\}$,
--   $$D_g:=\sum_x(-1)^{g(x)}|x\rangle\langle x|,\qquad|\varphi_g\rangle:=D_g|+\rangle^{\otimes m}=\frac1{\sqrt{2^m}}\sum_x(-1)^{g(x)}|x\rangle.$$
--   $O_f$ is the query unitary $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$; $\Delta_ag(x):=g(x)\oplus g(x\oplus a)$; the iterated differences are $g_0=g$, $g_i=\Delta_{a_i}g_{i-1}$; and $a_S=\bigoplus_{i\in S}a_i$ with $a_\emptyset=0^m$.
--
--   These are the objects of the phase-state injection that replaces oracle queries by resource states.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Definition 4.9; Lemma 4.11, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_Bits

open Matrix

namespace UnitaryQIPPSPACE

/-- **Boolean phase gate** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held
version sha256 9e357a00…, Definition 4.9, p. 26 (PDF p. 28)): "For a Boolean function
`g : {0,1}^m → {0,1}`, its associated Boolean phase gate `D_g` and phase state `|φ_g⟩` are defined as
`D_g := ∑_{x ∈ {0,1}^m} (−1)^{g(x)} |x⟩⟨x|`, `|φ_g⟩ := D_g |+⟩^{⊗m} = (1/√2^m) ∑_x (−1)^{g(x)} |x⟩`." -/
def boolPhaseGate {m : ℕ} (g : Bits m → Bool) : Matrix (Bits m) (Bits m) ℂ :=
  Matrix.diagonal fun x => if g x then -1 else 1

/-- **Boolean phase state** `|φ_g⟩ = (1/√2^m) ∑_x (−1)^{g(x)} |x⟩` (Definition 4.9, p. 26). -/
noncomputable def boolPhaseState {m : ℕ} (g : Bits m → Bool) : Bits m → ℂ :=
  fun x => (1 / (Real.sqrt (2 ^ m) : ℂ)) * (if g x then -1 else 1)

/-- The **query unitary** `O_f` on `ℓ + 1` qubits, `|x, b⟩ ↦ |x, b ⊕ f(x)⟩` (p. 9, PDF p. 11), with
`x` the first `ℓ` qubits and `b` the last. -/
def boolOracle {ℓ : ℕ} (f : Bits ℓ → Bool) : Matrix (Bits (ℓ + 1)) (Bits (ℓ + 1)) ℂ :=
  fun u' u => if Fin.init u' = Fin.init u ∧ u' (Fin.last ℓ) = Bool.xor (u (Fin.last ℓ)) (f (Fin.init u))
    then 1 else 0

/-- The **difference** `Δ_a g(x) := g(x) ⊕ g(x ⊕ a)` (p. 27, PDF p. 29). -/
def bdelta {m : ℕ} (a : Bits m) (g : Bits m → Bool) : Bits m → Bool :=
  fun x => Bool.xor (g x) (g (Bits.xor x a))

/-- **Iterated differences** (Lemma 4.11, p. 27): `g₀ := g`, `g_i := Δ_{a_i} g_{i−1}`;
`iterDiff g [a₁, …, a_j] = g_j`. -/
def iterDiff {m : ℕ} (g : Bits m → Bool) (as : List (Bits m)) : Bits m → Bool :=
  as.foldl (fun h a => bdelta a h) g

/-- `a_S := ⊕_{i ∈ S} a_i` for `S ⊆ [j]`, with `a_∅ = 0^m` (Lemma 4.11, p. 27): bit `k` is the
parity of the number of `i ∈ S` with `(a_i)_k = 1`. -/
def xorSet {m j : ℕ} (a : Fin j → Bits m) (S : Finset (Fin j)) : Bits m :=
  fun k => decide (Odd (S.filter fun i => a i k = true).card)

end UnitaryQIPPSPACE


