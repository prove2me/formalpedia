-- Prove2me | Definitions.Def_LiuHelsenDesigns_OneD_commutants
-- name    : LiuHelsenDesigns_OneD_commutants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:08:22.506293+00:00
-- url     : https://prove2.me/theorems/95a91333-19ed-46da-91c2-eeb7644a8be7
-- title:
--   Stochastic Lagrangian commutants and inverse Gram matrices
-- statement:
--   For positive order $k$, a stochastic Lagrangian is a $k$-dimensional binary subspace containing the all-ones vector and satisfying the integer quadratic congruence $x\cdot x-y\cdot y=0\pmod4$. The permutation sector consists of coordinate-permutation graphs.
--
--   $$G_C(T,S)=2^{q\dim(T\cap S)},\quad Wg_C=G_C^{-1},\quad f_\ell(T)=\|\Phi_{H,\ell}^{(k)}(R_\ell(T))\|_{2\to2}.$$
--
--   The Haar Gram matrix is the restriction to the permutation sector. Inverses and row-sum norms are computed from these matrices, not supplied as variables. The suppression function uses the local system size ℓ. The defining row-sum supremum has finite range and includes zero explicitly.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), pp.13–18, Definition 6, Eqs.(29)–(68). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_designs

noncomputable section
open scoped BigOperators

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev BinaryVector (k : ℕ) := (Fin k → ZMod 2) × (Fin k → ZMod 2)

/-- The quadratic condition is computed in integers before reducing modulo four. -/
def stochastic (k : ℕ) (T : Submodule (ZMod 2) (BinaryVector k)) : Prop :=
  Module.finrank (ZMod 2) T = k ∧ (1,1) ∈ T ∧
    ∀ v ∈ T, (∑ i, ((v.1 i).val : ℤ)^2 - ∑ i, ((v.2 i).val : ℤ)^2) % 4 = 0
abbrev Sigma (k : ℕ) := {T : Submodule (ZMod 2) (BinaryVector k) // stochastic k T}
instance sigmaFintype (k : ℕ) : Fintype (Sigma k) := Fintype.ofFinite _

def PermutationSector {k : ℕ} (T : Sigma k) : Prop :=
  ∃ π : Equiv.Perm (Fin k), ∀ v : BinaryVector k,
    v ∈ T.val ↔ v.2 = fun i => v.1 (π.symm i)
abbrev PermSector (k : ℕ) := {T : Sigma k // PermutationSector T}
instance permSectorFintype (k : ℕ) : Fintype (PermSector k) := Fintype.ofFinite _

def gramC (q k : ℕ) : Matrix (Sigma k) (Sigma k) ℝ :=
  fun T S => 2 ^ (q * Module.finrank (ZMod 2)
    ↥(T.val ⊓ S.val : Submodule (ZMod 2) (BinaryVector k)))
def gramH (q k : ℕ) : Matrix (PermSector k) (PermSector k) ℝ :=
  fun T S => gramC q k T.val S.val
def wgC (q k : ℕ) := (gramC q k)⁻¹
def wgH (q k : ℕ) := (gramH q k)⁻¹

/-- Row sums are finite; zero is adjoined explicitly for the empty-index case. -/
def eta (q k : ℕ) : ℝ :=
  sSup (insert 0 (Set.range (fun T : Sigma k =>
    ∑ S : Sigma k, |((2 : ℝ)^(q*k) • wgC q k)⁻¹ T S - (1 : Matrix (Sigma k) (Sigma k) ℝ) T S|)))

def commutantMatrix (q k : ℕ) (T : Sigma k) : CopyMat q k :=
  fun x y => ∏ j : Fin q,
    if ((fun i => (boolNat (x i j) : ZMod 2)),
        (fun i => (boolNat (y i j) : ZMod 2))) ∈ T.val then 1 else 0

def suppression (ℓ k : ℕ) (T : Sigma k) : ℝ :=
  matrixNorm (twirl (haar ℓ) k (commutantMatrix ℓ k T))

end LiuHelsenDesigns.OneD


