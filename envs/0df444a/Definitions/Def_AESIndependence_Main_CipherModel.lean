-- Prove2me | Definitions.Def_AESIndependence_Main_CipherModel
-- name    : AESIndependence_Main_CipherModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T04:10:10.004536+00:00
-- url     : https://prove2.me/theorems/9c5948ce-2d87-4e84-a4c3-66c712ce42b6
-- title:
--   Generalized AES layers and independent round-key law
-- statement:
--   A cipher is specified by a field $F$ with an arbitrary $b$-element basis over $\mathbb F_2$, an invertible binary-linear byte map $A$, and an invertible $F$-linear column map $C$. Every entry of the matrix of $C$ and its inverse is nonzero. States are $d\times d$ arrays over $F$, with $n=bd^2$ binary coordinates. Matrix linear equivalences encode precisely the source matrices; no field-linearity is imposed on $A$.
--   The patched inverse is $\iota(z)=z^{-1}$, with $\iota(0)=0$. SubBytes applies $A\iota$ bytewise, ShiftRows sends $x$ to $y_{ij}=x_{i,i+j\bmod d}$, and MixColumns applies $C$ independently to each column. Thus $M=M_{\rm MC}M_{\rm SR}A\iota$ and $M_{\rm lin}=M_{\rm MC}M_{\rm SR}A$. Key addition is $T_k(x)=x+k$.
--   Encryption is the concrete recursion
--   $$F^0(x)=T_{K_0}(x),\qquad F^{i+1}(x)=T_{K_{i+1}}M(F^i(x)).$$
--   The ciphertext law draws the entire list $K_0,\ldots,K_r$ uniformly from the finite product state space, then applies the same resulting permutation to all plaintexts. Its comparison law is uniform on ordered injective tuples $\Omega_t$, rather than the product law allowing collisions.
--   The chain $P$ applies $T_{k'}MT_k$ using two uniform keys. The matrix $W=(P^3)^\mathsf TP^3$ and the separate seven-key action
--   $$W(v)=T_{v_0}M^{-1}T_{v_1}M^{-1}T_{v_2}M^{-1}T_{v_3}MT_{v_4}MT_{v_5}MT_{v_6}$$
--   are both defined. Identifying their laws is a solver obligation. Finally $\operatorname{Tr}(z)=\sum_{r=0}^{b-1}z^{2^r}$ is stored as its value in $F$, the canonical embedding of the binary trace.
--   These definitions retain the actual cipher rather than assuming any spectral or independence conclusion. **Formalization Note** ShiftRows uses powers of the standard cyclic rotation of `Fin d`, exactly the indicated modular addition. Every round retains MixColumns. Algebra over $\mathbb F_2$ fixes characteristic two, and the basis fixes field cardinality $2^b$.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), §2.1 and Definitions 2.2–2.13, Eq. (2.1), pp.9–12 (PDF pp.9–12)

import Mathlib
import Definitions.Def_AESIndependence_Main_LabelChains

namespace AESIndependence.Main
noncomputable section
open scoped BigOperators Classical

abbrev ByteIndex (d : ℕ) := Fin d × Fin d
abbrev State (d : ℕ) (F : Type) := ByteIndex d → F
abbrev BitIndex (b d : ℕ) := ByteIndex d × Fin b
abbrev BinaryState (ι : Type) := ι → ZMod 2

def bitCount (b d : ℕ) : ℕ := b * d^2

/-- C is represented by its invertible column-linear map; its matrix entries and
inverse entries are evaluated on the standard coordinate vectors. No MDS condition. -/
structure Cipher (b d : ℕ) (F : Type) [Field F] [Algebra (ZMod 2) F] where
  basis : Module.Basis (Fin b) (ZMod 2) F
  A : F ≃ₗ[ZMod 2] F
  C : (Fin d → F) ≃ₗ[F] (Fin d → F)
  C_nonzero : ∀ i j, C (Pi.single j 1) i ≠ 0
  C_inv_nonzero : ∀ i j, C.symm (Pi.single j 1) i ≠ 0

variable {b d : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- Every bit of every byte in the given binary basis. -/
def stateCoordinates (D : Cipher b d F) : State d F ≃ BinaryState (BitIndex b d) where
  toFun x p := D.basis.equivFun (x p.1) p.2
  invFun x q := D.basis.equivFun.symm (fun r => x (q,r))
  left_inv x := by funext q; simp
  right_inv x := by
    funext p
    exact congrFun (D.basis.equivFun.apply_symm_apply (fun r => x (p.1,r))) p.2

def translation (v : State d F) : Equiv.Perm (State d F) where
  toFun x := x + v
  invFun x := x - v
  left_inv x := add_sub_cancel_right x v
  right_inv x := sub_add_cancel x v

/-- Field inverse already patches zero to zero. -/
def inversion : Equiv.Perm (State d F) where
  toFun x q := (x q)⁻¹
  invFun x q := (x q)⁻¹
  left_inv x := by funext q; simp
  right_inv x := by funext q; simp

def byteLinear (D : Cipher b d F) : Equiv.Perm (State d F) :=
  Equiv.piCongrRight (fun _ => D.A.toEquiv)

/-- y(i,j) = x(i,i+j), with Fin addition modulo d. -/
def shiftRows : Equiv.Perm (State d F) where
  toFun x q := x (q.1, (finRotate d ^ q.1.val) q.2)
  invFun x q := x (q.1, (finRotate d ^ q.1.val).symm q.2)
  left_inv x := by funext q; simp
  right_inv x := by funext q; simp

/-- Each column is acted on by precisely C. -/
def mixColumns (D : Cipher b d F) : Equiv.Perm (State d F) where
  toFun x q := D.C (fun i => x (i,q.2)) q.1
  invFun x q := D.C.symm (fun i => x (i,q.2)) q.1
  left_inv x := by funext q; exact congrFun (D.C.symm_apply_apply (fun i => x (i,q.2))) q.1
  right_inv x := by funext q; exact congrFun (D.C.apply_symm_apply (fun i => x (i,q.2))) q.1

def linearLayer (D : Cipher b d F) : Equiv.Perm (State d F) :=
  mixColumns D * shiftRows * byteLinear D

def roundPermutation (D : Cipher b d F) : Equiv.Perm (State d F) :=
  linearLayer D * inversion

/-- All r+1 keys are retained; key 0 precedes the r actual rounds. -/
def encrypt (D : Cipher b d F) : (r : ℕ) →
    (Fin (r+1) → State d F) → Equiv.Perm (State d F)
  | 0, k => translation (k 0)
  | r+1, k => translation (k (Fin.last (r+1))) * roundPermutation D *
      encrypt D r (fun i => k i.castSucc)

/-- The pushforward of the uniform finite product key law under tuple encryption. -/
def ciphertextLaw [Fintype F] (D : Cipher b d F) {t : ℕ}
    (r : ℕ) (x : DistinctTuple (State d F) t) :
    PMF (DistinctTuple (State d F) t) :=
  (PMF.uniformOfFintype (Fin (r+1) → State d F)).map
    (fun k => tuplePerm (encrypt D r k) x)

def cipherTV [Fintype F] (D : Cipher b d F) {t : ℕ}
    (r : ℕ) (x : DistinctTuple (State d F) t) : ℝ :=
  totalVariation (fun y => (ciphertextLaw D r x y).toReal)
    (uniformMass (DistinctTuple (State d F) t))

def pChain [Fintype F] (D : Cipher b d F) (t : ℕ) :
    LabelChain (DistinctTuple (State d F) t) (Fin 2 → State d F) where
  law := PMF.uniformOfFintype _
  action k := tuplePerm (translation (k 1) * roundPermutation D * translation (k 0))

abbrev WLabel (d : ℕ) (F : Type) := Fin 7 → State d F

/-- Equation (2.1), with the rightmost factor applied first. -/
def wPermutation (D : Cipher b d F) (v : WLabel d F) : Equiv.Perm (State d F) :=
  translation (v 0) * (roundPermutation D)⁻¹ * translation (v 1) *
  (roundPermutation D)⁻¹ * translation (v 2) * (roundPermutation D)⁻¹ *
  translation (v 3) * roundPermutation D * translation (v 4) *
  roundPermutation D * translation (v 5) * roundPermutation D * translation (v 6)

def wChain [Fintype F] (D : Cipher b d F) (t : ℕ) :
    LabelChain (DistinctTuple (State d F) t) (WLabel d F) where
  law := PMF.uniformOfFintype _
  action v := tuplePerm (wPermutation D v)

/-- W=(P^3)^T P^3, in the column convention. The equality with the seven-key
label matrix is a proof obligation, not a field of Cipher. -/
def wMatrix [Fintype F] (D : Cipher b d F) (t : ℕ) :
    Matrix (DistinctTuple (State d F) t) (DistinctTuple (State d F) t) ℝ :=
  (((pChain D t).matrix)^3).transpose * ((pChain D t).matrix)^3

def traceByte (b : ℕ) (z : F) : F := ∑ r : Fin b, z ^ (2 ^ r.val)

end
end AESIndependence.Main


