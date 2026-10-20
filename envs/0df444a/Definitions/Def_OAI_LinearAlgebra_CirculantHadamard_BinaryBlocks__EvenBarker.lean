-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:09:55.31485+00:00
-- url     : https://prove2.me/theorems/089ed58d-7d54-4f5c-93db-0bd6b3bff952
-- title:
--   Four-block decomposition and partial evaluation at a fourth root
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Product group ring.** $R[\mathbb Z/4\times\mathbb Z/m]$.
--   2. **CRT reindexing.** For odd $u$, $\gcd(4,u^2)=1$, and the Chinese remainder isomorphism $\mathbb Z/4u^2\cong\mathbb Z/4\times\mathbb Z/u^2$ induces an $R$-algebra isomorphism
--   $$
--   R[\mathbb Z/4u^2]\;\cong\;R[\mathbb Z/4\times\mathbb Z/u^2].
--   $$
--   3. **Blocks.** For $f\in R[\mathbb Z/4\times\mathbb Z/m]$ and $j\in\mathbb Z/4$, the block $f_j\in R[\mathbb Z/m]$ with $f_j(b)=f(j,b)$; the four blocks are indexed by $j=0,1,2,3$, and a coefficient map $\varphi$ can be applied to each block.
--   4. **Partial evaluation.** For $\varphi:R\to S$ and $z\in S$ with $z^4=1$, the ring homomorphism $R[\mathbb Z/4\times\mathbb Z/m]\to S[\mathbb Z/m]$ sending $r\,e_{(a,b)}$ to $\varphi(r)z^{a}\,e_b$. It evaluates the $\mathbb Z/4$ coordinate at $z$ and keeps the $\mathbb Z/m$ coordinate. Any $i$ with $i^2=-1$ satisfies $i^4=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryBlocks.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryBlocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving__EvenBarker

namespace OAI

universe uR uS

/-!
# The actual four-block decomposition and partial evaluations

The Chinese remainder equivalence transports the actual cyclic group ring,
not just a coefficient count. Coefficients of its four slices are the original
signs. Partial evaluation is a ring homomorphism defined on the product group
algebra and intertwines coefficient conjugation with index reversal.
-/

noncomputable section

namespace CirculantHadamard.BinaryBlocks

open CyclicRing
open scoped BigOperators

abbrev ProductElem (R : Type uR) [Semiring R] (m : ℕ) :=
  AddMonoidAlgebra R (ZMod 4 × ZMod m)

theorem four_coprime_sq {u : ℕ} (hu : Odd u) : Nat.Coprime 4 (u ^ 2) := by
  simpa using (hu.coprime_two_left.pow_left 2).pow_right 2

/-- The concrete CRT map on the exponent group. -/
def crtIndex (u : ℕ) (hu : Odd u) :
    ZMod (4 * u ^ 2) ≃+ ZMod 4 × ZMod (u ^ 2) :=
  (ZMod.chineseRemainder (four_coprime_sq hu)).toAddEquiv

/-- The resulting algebra equivalence preserves the actual convolution. -/
def crt (R : Type uR) [CommRing R] (u : ℕ) (hu : Odd u) :
    Elem R (4 * u ^ 2) ≃ₐ[R] ProductElem R (u ^ 2) :=
  AddMonoidAlgebra.domCongr R R (crtIndex u hu)

@[simp] theorem crt_apply {R : Type uR} [CommRing R] {u : ℕ} (hu : Odd u)
    (f : Elem R (4 * u ^ 2)) (a : ZMod 4 × ZMod (u ^ 2)) :
    (crt R u hu f).coeff a = f.coeff ((crtIndex u hu).symm a) := by
  exact AddMonoidAlgebra.coeff_domCongr (R := R) (A := R) (crtIndex u hu) f a

def block {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : ZMod 4) : Elem R m :=
  ofCoeffs fun b => f.coeff (j, b)

@[simp] theorem block_apply {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : ZMod 4) (b : ZMod m) : (block f j).coeff b = f.coeff (j, b) := rfl

/-- Fin-four indexing agrees with the coefficient arithmetic used by the halves. -/
def blocks {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) : Fin 4 → Elem R m := fun j => block f j

@[simp] theorem blocks_apply {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : Fin 4) (b : ZMod m) : (blocks f j).coeff b = f.coeff (j, b) := rfl

section Evaluation

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (m : ℕ)

/-- A fourth-root character on the first factor, retaining the second factor. -/
def partialCharacter (z : S) (hz : z ^ 4 = 1) :
    Multiplicative (ZMod 4 × ZMod m) →* Elem S m where
  toFun a := AddMonoidAlgebra.single a.toAdd.2
    (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd a.toAdd.1))
  map_one' := by
    change AddMonoidAlgebra.single 0
      (CyclicPolynomial.powerCharacter 4 z hz 1) = 1
    rw [map_one]
    rfl
  map_mul' a b := by
    change AddMonoidAlgebra.single (a.toAdd.2 + b.toAdd.2)
      (CyclicPolynomial.powerCharacter 4 z hz
        (Multiplicative.ofAdd a.toAdd.1 * Multiplicative.ofAdd b.toAdd.1)) =
      AddMonoidAlgebra.single a.toAdd.2
        (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd a.toAdd.1)) *
      AddMonoidAlgebra.single b.toAdd.2
        (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd b.toAdd.1))
    rw [map_mul, AddMonoidAlgebra.single_mul_single]

/-- Actual partial evaluation, allowing the integer-to-complex coefficient map. -/
def partialEval (φ : R →+* S) (z : S) (hz : z ^ 4 = 1) :
    ProductElem R m →+* Elem S m :=
  AddMonoidAlgebra.liftNCRingHom
    (AddMonoidAlgebra.singleZeroRingHom.comp φ) (partialCharacter m z hz)
    (fun _ _ => Commute.all _ _)

@[simp] theorem partialEval_single (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (a : ZMod 4 × ZMod m) (r : R) :
    partialEval m φ z hz (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single a.2 (φ r * z ^ a.1.val) := by
  simp [partialEval, AddMonoidAlgebra.liftNCRingHom,
    AddMonoidAlgebra.liftNC_single, partialCharacter,
    AddMonoidAlgebra.single_mul_single]

variable [NeZero m]

def mappedBlock (φ : R →+* S) (f : ProductElem R m) (j : ZMod 4) : Elem S m :=
  ofCoeffs fun b => φ (f.coeff (j, b))

@[simp] theorem mappedBlock_apply (φ : R →+* S) (f : ProductElem R m)
    (j : ZMod 4) (b : ZMod m) : (mappedBlock m φ f j).coeff b = φ (f.coeff (j, b)) := rfl

theorem fourthRoot_pow_four (i : S) (hi : i ^ 2 = -1) : i ^ 4 = 1 := by
  calc
    i ^ 4 = (i ^ 2) ^ 2 := by ring
    _ = 1 := by rw [hi]; norm_num

end Evaluation

section Star

variable {R : Type uR} {S : Type uS} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable (m : ℕ) [NeZero m]

end Star

end CirculantHadamard.BinaryBlocks

end

end OAI


