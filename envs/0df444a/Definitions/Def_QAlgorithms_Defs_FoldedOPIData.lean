-- Prove2me | Definitions.Def_QAlgorithms_Defs_FoldedOPIData
-- name    : QAlgorithms_Defs_FoldedOPIData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:34:25.025997+00:00
-- url     : https://prove2.me/theorems/96e47c2d-0953-48df-946d-05c88b299494
-- title:
--   FoldedOPIData
-- statement:
--   FoldedOPIData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FoldedOPIData.lean

import Definitions.Def_QAlgorithms_Defs_ReedSolomonDecoders
import Definitions.Def_QAlgorithms_Defs_FiniteOraclePrograms
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.FoldedOPI

/-- Admissible public folded-family domain; 2610.02145 pp.13–14.
All derived dimensions are computed from M and rational R. -/
structure PublicDomain where
  M : ℕ
  M_pos : 0 < M
  rate : ℚ
  rate_pos : 0 < rate
  rate_lt : rate < 1
  u : ℕ
  u_pos : 0 < u
  power : M+1 = 2^u
  enough : M+2 ≤ ⌊rate*((M+2)*M)⌋₊

/-- Computed (h,N,q,K,J,ell); 2610.02145 pp.13–14,19,32. -/
def publicParameters (P : PublicDomain) : Fin 6 → ℕ :=
  let h := P.M+2
  let N := h*P.M
  let K := ⌊P.rate*N⌋₊
  let J := K/h
  ![h,N,N+1,K,J,(J-1)/2]

/-- The actual characteristic-two field, not ZMod q;
2610.02145 pp.9,14. Its effective public basis/primitive-element construction is
realized by the public bit constructor of a compiled family. -/
abbrev publicField (P : PublicDomain) := GaloisField 2 (2*P.u)

/-- Finiteness of the actual chosen field; 2610.02145 pp.9,14. -/
noncomputable instance publicFieldFintype (P : PublicDomain) : Fintype (publicField P) :=
  Fintype.ofFinite _

/-- Polynomial-basis public representation and primitive generator, chosen before oracles;
2610.02145 pp.14,16,40. Costs are charged by the public constructor. -/
structure PublicFieldData (P : PublicDomain) where
  encoding : OPI.publicFieldEncoding (publicField P)
  effective : OPI.EffectiveFieldEncoding encoding
  gamma : publicField P
  primitive : orderOf gamma = (publicParameters P 2)-1
  generator_nonzero : gamma ≠ 0

/-- Row-major regrouping at scalar coordinate ih+j;
2610.02145 p.9 (2.3). -/
def foldEquiv (F : Type*) (M h : ℕ) : (Fin (M*h) → F) ≃ (Fin M → Fin h → F) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl F)).trans (Equiv.curry _ _ _)

/-- Linear folded image of the actual scalar code;
2610.02145 p.9 (2.4), p.11 (2.15). -/
def foldedCode {F : Type*} [Field F] (M h : ℕ)
    (C : Submodule F (Fin (M*h) → F)) : Submodule F (Fin M → Fin h → F) :=
  C.map ({
    toFun := foldEquiv F M h
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; ext i j; rfl } :
      (Fin (M*h) → F) →ₗ[F] (Fin M → Fin h → F))

/-- Shared Vandermonde encoder followed by folding;
2610.02145 p.14 (3.3). -/
def encoder {F : Type*} [Field F] (M h K : ℕ) (gamma : F) (x : Fin K → F) :
    Fin M → Fin h → F :=
  foldEquiv F M h ((OPI.vandermondeEncoder (fun t : Fin (M*h) => gamma^t.val) K).mulVec x)

/-- Arbitrary joint half-alphabet predicates, fixed public code;
2610.02145 p.14, Definition 5. -/
structure BalancedInstance (M : ℕ) (Sigma : Type*) [Fintype Sigma] [Nonempty Sigma] where
  sets : Fin M → Finset Sigma
  balanced : ∀ i, 2*(sets i).card = Fintype.card Sigma

/-- Full-block accepted fraction on positive M; 2610.02145 p.14 (3.5). -/
def score {F : Type*} [Field F] [Fintype F] {M h K : ℕ} (_hM : 0 < M)
    (gamma : F) (A : BalancedInstance M (Fin h → F)) (x : Fin K → F) : ℝ :=
  ((Finset.univ.filter fun i => encoder M h K gamma x i ∈ A.sets i).card : ℝ)/M

/-- Local signed predicate without a normalization of f_i(0);
2610.02145 pp.17,39 (4.1), Lemma 7. -/
def localSign {Sigma : Type*} (A : Finset Sigma) (z : Sigma) : ℝ :=
  if z ∈ A then 1 else -1

/-- Actual signed block objective; 2610.02145 p.17 (4.1). -/
def signedObjective {F : Type*} [Field F] [Fintype F] {M h K : ℕ}
    (gamma : F) (A : BalancedInstance M (Fin h → F)) (x : Fin K → F) : ℝ :=
  ∑ i, localSign (A.sets i) (encoder M h K gamma x i)

/-- Separately labelled ordinary XOR block oracles; 2610.02145 p.13 (2.25).
A caller must use the fixed label as structural circuit data. No multiplexing
or primitive controlled query is introduced. -/
def fixedBlockOracles {Sigma : Type*} [DecidableEq Sigma] {M : ℕ}
    (sets : Fin M → Finset Sigma) (i : Fin M) : Matrix (Sigma × Bool) (Sigma × Bool) ℂ :=
  xorOracle fun z => decide (z ∈ sets i)

/-- Fixed polynomial-basis embedding of one complete symbol and its answer;
2610.02145 pp.13–14,40. Unused code-space encodings have a fixed extension. -/
def blockOracleEmbedding {F : Type} [Field F] [Fintype F]
    (E : OPI.publicFieldEncoding F) (h : ℕ) :
    Matrix (Qubits (h*(E.e*Nat.clog 2 E.p)+1)) ((Fin h → F) × Bool) ℂ :=
  Matrix.of fun z input =>
    let bits := (List.ofFn fun i : Fin h => OPI.fieldBits E (input.1 i)).flatten
    if z = Fin.snoc (fun i : Fin (h*(E.e*Nat.clog 2 E.p)) => bits.getD i.val false) input.2
    then 1 else 0

/-- Independent uniform half-size subsets at every block;
2610.02145 pp.15–16,21. Within a block the bits are not independent. -/
def sampledInstanceLaw (M : ℕ) (Sigma : Type*) [Fintype Sigma] [Nonempty Sigma]
    [Nonempty {A : Finset Sigma // 2*A.card = Fintype.card Sigma}] :
    PMF (BalancedInstance M Sigma) :=
  (PMF.uniformOfFintype (Fin M → {A : Finset Sigma // 2*A.card = Fintype.card Sigma})).map
    fun A => ⟨fun i => (A i).val, fun i => (A i).property⟩

/-- Classical and quantum limiting scores for a fixed rational rate;
2610.02145 p.15 (3.6). -/
def scoreLevels (R : ℚ) (_hR : 0 < R ∧ R < 1) : ℝ × ℝ :=
  ((1+(R : ℝ))/2,(1+Real.sqrt ((R : ℝ)*(2-(R : ℝ))))/2)

example {F : Type*} [Field F] (M h : ℕ) (x : Fin (M*h) → F) :
    (foldEquiv F M h).symm (foldEquiv F M h x) = x :=
  (foldEquiv F M h).symm_apply_apply x

example {Sigma : Type*} (z : Sigma) : localSign ∅ z = -1 := by simp [localSign]

end QAlgorithms.FoldedOPI


