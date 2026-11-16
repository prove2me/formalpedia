-- Prove2me | Definitions.Def_CyclicForrelation_Even_Supplement_hiddenSubspace
-- name    : CyclicForrelation_Even_Supplement_hiddenSubspace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:56.635229+00:00
-- url     : https://prove2.me/theorems/759e33aa-6f28-4381-8b24-86e8a999c80f
-- title:
--   Hidden-subspace oracle distribution and parity-dependent padding
-- statement:
--   Let $G=\mathbb F_2^n$. The **binary orthogonal complement** of a subspace $L\le G$ is $L^\perp=\{x:\langle y,x\rangle=0\text{ for every }y\in L\}$, using the binary dot product. Choose $L$ uniformly among all subspaces with dimension $\lfloor n/2\rfloor$. Conditional on $L$, choose independent uniform $s,t\in G$, $\sigma\in\{-1,1\}$, and sign functions $\phi:G/L\to\{-1,1\}$, $\psi:G/L^\perp\to\{-1,1\}$ (all their entries are independent uniform signs). Define
--   $$\begin{aligned}f_1(x)&=\chi_s(x)\phi(x+L),&f_3(x)&=\chi_s(x)\phi(x+t+L),\\f_2(x)&=\chi_t(x)\psi(x+L^\perp),&f_4(x)&=\sigma\chi_s(t)\chi_t(x)\psi(x+s+L^\perp).\end{aligned}$$
--   The **hard-input distribution** is the pushforward of that concrete finite probability law through the displayed four-oracle construction. For even $k\ge4$, append $k-4$ known constant-one oracles. For odd $k\ge5$, apply the quadratic cap to the four-oracle tuple, then append $k-5$ constant-one oracles.
--
--   This supplies the paper's input distribution for analyzing adaptive algorithms. The assertions $T_4=\sigma$, $T_5=\sigma c_n$, the coupling, and the collision bounds remain to be proved; neither the adaptive complexity nor its input domain is restricted by this distribution.
--
--   **Formalization Note** Subspaces and quotients use Mathlib's general `Submodule` infrastructure. The uniform law first samples a half-dimensional subspace and then the independent product conditional on that subspace, so there is no unintended size bias from dependent quotient spaces. Existence of a half-dimensional subspace follows from the finite-dimensional basis API and is proved before uniform sampling. Quotient labels are actual quotient classes; sign multiplication is XOR. Padding uses Boolean false ($+1$). The total definitions at $k<4$ are outside Theorem 16's domain.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), pp. 21–22, proof of Theorem 16

import Definitions.Def_CyclicForrelation_Even_Supplement_quadraticCap

namespace CyclicForrelation.Even.Supplement

/-- Orthogonal complement for the binary dot product on the published cube. -/
def binaryOrthogonal {n : ℕ} (L : Submodule (ZMod 2) (Cube n)) :
    Submodule (ZMod 2) (Cube n) :=
  L.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2))

/-- Exactly the subspaces of dimension floor(n/2); this is not an oracle promise. -/
abbrev HalfSubspace (n : ℕ) :=
  {L : Submodule (ZMod 2) (Cube n) // Module.finrank (ZMod 2) L = n / 2}

noncomputable instance halfSubspaceFintype (n : ℕ) : Fintype (HalfSubspace n) :=
  Fintype.ofFinite _

/-- A coordinate-independent existence API for the finite uniform sampling type. -/
instance halfSubspaceNonempty (n : ℕ) : Nonempty (HalfSubspace n) := by
  have hdim : n / 2 ≤ Module.finrank (ZMod 2) (Cube n) := by
    simpa [Cube] using (Nat.div_le_self n 2)
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  exact ⟨⟨Submodule.span (ZMod 2) (Set.range v), by
    simpa using finrank_span_eq_card hv⟩⟩

/-- Given L, independent shifts s,t, hidden sign σ, and signs on the two quotient spaces. -/
abbrev HiddenSeed {n : ℕ} (L : Submodule (ZMod 2) (Cube n)) :=
  Cube n × Cube n × Bool × (Cube n ⧸ L → Bool) × (Cube n ⧸ binaryOrthogonal L → Bool)

noncomputable instance hiddenSeedFintype {n : ℕ} (L : Submodule (ZMod 2) (Cube n)) :
    Fintype (HiddenSeed L) := Fintype.ofFinite _

/-- The four source oracles, with false = +1 and multiplication represented by XOR. -/
def hiddenFourTuple {n : ℕ} (L : Submodule (ZMod 2) (Cube n))
    (r : HiddenSeed L) : OracleTuple n 4 :=
  let s := r.1
  let t := r.2.1
  let σ := r.2.2.1
  let φ := r.2.2.2.1
  let ψ := r.2.2.2.2
  fun j x => match j.val with
  | 0 => Bool.xor (characterBit s x) (φ (Submodule.Quotient.mk x))
  | 1 => Bool.xor (characterBit t x) (ψ (Submodule.Quotient.mk x))
  | 2 => Bool.xor (characterBit s x) (φ (Submodule.Quotient.mk (x + t)))
  | _ => Bool.xor σ (Bool.xor (characterBit s t)
      (Bool.xor (characterBit t x) (ψ (Submodule.Quotient.mk (x + s)))))

/-- First choose L uniformly, then choose the independent finite product given L.
Uniformity, trace identities and collision bounds are never validity assumptions. -/
noncomputable def hiddenFourLaw (n : ℕ) : PMF (OracleTuple n 4) :=
  (PMF.uniformOfFintype (HalfSubspace n)).bind fun L =>
    (PMF.uniformOfFintype (HiddenSeed L.val)).map (hiddenFourTuple L.val)

/-- Append known +1 oracles; the source uses even numbers of appended factors. -/
def padOnes {n a : ℕ} (g : OracleTuple n a) (k : ℕ) : OracleTuple n k :=
  fun j x => if h : j.val < a then g ⟨j.val, h⟩ x else false

/-- The source hard input for every k ≥ 4, using the cap for odd lengths.
Values at k < 4 are harmless totalization and are never used by Theorem 16. -/
def hiddenTuple {n : ℕ} (k : ℕ) (L : Submodule (ZMod 2) (Cube n))
    (r : HiddenSeed L) : OracleTuple n k :=
  if k % 2 = 0 then padOnes (hiddenFourTuple L r) k
  else padOnes (oddLift (hiddenFourTuple L r)) k

noncomputable def hiddenLaw (n k : ℕ) : PMF (OracleTuple n k) :=
  (PMF.uniformOfFintype (HalfSubspace n)).bind fun L =>
    (PMF.uniformOfFintype (HiddenSeed L.val)).map (hiddenTuple k L.val)

end CyclicForrelation.Even.Supplement


