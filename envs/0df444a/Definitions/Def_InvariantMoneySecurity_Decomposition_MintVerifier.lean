-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_MintVerifier
-- name    : InvariantMoneySecurity_Decomposition_MintVerifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:31.275804+00:00
-- url     : https://prove2.me/theorems/59c94fef-7e38-4204-a7b5-33f481231520
-- title:
--   Algorithm 1 — the lazy verifier and the measured mint law
-- statement:
--   For public serial $p$ and any round count $r$, the accepting Kraus operator of Algorithm 1 is $K_{p,r}=\widehat B^r\Pi_{P_p}$. The accepting state is the subnormalized branch $K_{p,r}\rho K_{p,r}^*$. The verifier effect and probability are
--   $$E_{p,r}=\Pi_{P_p}\widehat B^{2r}\Pi_{P_p},\qquad \operatorname{Acc}_p(\rho)=\operatorname{Tr}(E_{p,r}\rho).$$
--   The controlled move operator uses $2|S|$ indices, with the first half applying actual moves and the second half applying the identity. Its register is initialized uniformly, giving the lazy factor $1/2$. Projection of that register back to its uniform state in each round gives precisely the finite-round Kraus operator above.
--
--   The measured mint law is represented by averaging uniformly over objects $x\in X$ and setting $p=I(x)$. Consequently the serial law has weight $|P_p|/|X|$, rather than being uniform on serials. Conditional on a genuine serial the coherent note is the uniform vector on $P_p$.
--
--   For two possibly entangled output registers, the success probability is the joint Born probability
--   $$\operatorname{Tr}\bigl[(E_{p,r}\otimes E_{p,r})\rho_{12}\bigr].$$
--   This formula preserves correlations between the outputs. Invalid serials and invalid object encodings have zero acceptance.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), pp. 7–8, equations (2)–(5), Algorithm 1 and Definition 2.2; p. 9, Definition 2.4

import Definitions.Def_InvariantMoneySecurity_Decomposition_Scheme
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition

/-- Algorithm 1's accepting Kraus operator, for any round count. -/
def FiniteScheme.acceptKraus {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) (r : ℕ) :=
  D.walk ^ r * D.serialProjector p

/-- The effect of the actual finite-round verifier, equation (5), not an ideal projector. -/
def FiniteScheme.verifyEffect {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) (r : ℕ) :=
  D.serialProjector p * D.walk ^ (2 * r) * D.serialProjector p

/-- The subnormalized state of the accepting branch. -/
def FiniteScheme.acceptBranch {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) (r : ℕ)
    (ρ : Matrix (Bits n) (Bits n) ℂ) :=
  D.acceptKraus p r * ρ * (D.acceptKraus p r).conjTranspose

/-- Equation (5), defined for mixed states and invalid serials as well. -/
def FiniteScheme.acceptance {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) (r : ℕ)
    (ρ : Matrix (Bits n) (Bits n) ℂ) := born (D.verifyEffect p r) ρ

/-- The actual mint law is represented by the uniform object average.
Grouping this average by invariant gives serial weight |P_p|/|X|. -/
def FiniteScheme.mintAverage {n : ℕ} (D : FiniteScheme n)
    (f : Bits D.serialBits → D.Object → ℝ) : ℝ :=
  (D.ground.card : ℝ)⁻¹ * ∑ x : D.Object, f (D.invariant x) x

/-- Joint Born probability for two output registers, even when they are entangled. -/
def FiniteScheme.jointAcceptance {n : ℕ} (D : FiniteScheme n) (p : Bits D.serialBits) (r : ℕ)
    (ρ : Matrix (Bits (n + n)) (Bits (n + n)) ℂ) : ℝ :=
  let E := D.verifyEffect p r
  let E₂ : Matrix (Bits (n + n)) (Bits (n + n)) ℂ := fun a b =>
    E (fun j => a (Fin.castAdd n j)) (fun j => b (Fin.castAdd n j)) *
    E (fun j => a (Fin.natAdd n j)) (fun j => b (Fin.natAdd n j))
  born E₂ ρ

/-- Uniform-move controlled unitary on the valid object subspace. Half its indices are identities.
The physical invalid-object subspace is rejected by the preceding serial check. -/
def FiniteScheme.controlledMove {n : ℕ} (D : FiniteScheme n) :
    Matrix (Fin (D.moveCount + D.moveCount) × D.Object)
      (Fin (D.moveCount + D.moveCount) × D.Object) ℂ :=
  fun a b => if a.1 = b.1 then
    if h : b.1.val < D.moveCount then
      if a.2 = D.move ⟨b.1.val, h⟩ b.2 then 1 else 0
    else if a.2 = b.2 then 1 else 0
  else 0

/-- Uniform move-register state in Algorithm 1, including the identity indices. -/
def FiniteScheme.moveRegister {n : ℕ} (D : FiniteScheme n) :
    Fin (D.moveCount + D.moveCount) → ℂ := uniformVector Finset.univ

end InvariantMoneySecurity.Decomposition


