-- Prove2me | Definitions.Def_CliffordCert_Optimal_Supplement_rank_protocol
-- name    : CliffordCert_Optimal_Supplement_rank_protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:38:31.919666+00:00
-- url     : https://prove2.me/theorems/60368dc0-b4d4-442f-b58d-067997a7144d
-- title:
--   Rank padding, leakage encoders and the support spectral test
-- statement:
--   For an integer rank $k\ge2$ and message dimension $r=2^q$, put $b=\lceil\log_2 k\rceil$, $K=2^b$, $a=\min\{q,b\}$ and $R=\min\{r,K\}=2^a$. Define
--
--   $$
--   F(q,k,\varepsilon)=\frac{k^3}{\min\{2^q,k\}^2\varepsilon^2},\qquad
--    t=\left\lceil\frac{64\ln3}{\varepsilon^2}\right\rceil,\qquad
--    s=\left\lceil\frac{512K}{\varepsilon^2}\right\rceil.
--   $$
--
--   Given support coordinates $J$, a $k$-to-$K$ isometry $A$, an $R$-to-$r$ isometry $B$ and a fixed $K$-to-$R$ Clifford family $\{\Psi_i\}_{i=1}^L$, the support encoders are $X\mapsto B\Psi_i(A\Gamma_\sigma(X)A^\dagger)B^\dagger$. The leakage encoder sends the quantum state
--
--   $$
--   \Lambda_P(X)=\operatorname{Tr}(PX)|0\rangle\langle0|+
--   \operatorname{Tr}((I-P)X)|1\rangle\langle1|,
--   $$
--
--   using two distinct computational codewords in the $r$-dimensional message. The fixed sender schedule has $t$ leakage senders followed by $L$ blocks of $s$ support senders. The collective acceptance operator requires all leakage outcomes to be zero and uses the published spectral block effect on the support messages at separation $\varepsilon/2$. Thus its threshold is the strict inequality $L^{-1}\sum_i Z_i<\beta/2$ with $\beta=\varepsilon^2/(4RL)$. Tensor isometric inclusion embeds the support effect into the allowed message system, rejecting the orthogonal complement. No separate classical outcome is sent.
--
--   The file also defines a finite list covering every channel in a physical protocol's fixed schedule. The length of such a list bounds the number of distinct settings. Raw encoders and acceptance operators carry no assumptions of positivity, trace preservation, compression, moments or success: those properties require valid geometric inputs and proofs. Theorem 5 states existence of a physical protocol with the two resource bounds.
--
--   **Formalization Note** The ceiling logarithm is the natural-number ceiling logarithm `Nat.clog 2 k`, not a real logarithm rounded down. The support block size is the published block size at $(b,\varepsilon/2)$. Sender order is leakage first, then block index, then position within block. The two leakage codewords are the all-zero word and the word with only the first bit set; they are distinct since $q\ge1$.
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 7 (PDF 8), Eqs. (7)–(8); pp. 18–20 (PDF 19–21), Eqs. (33)–(37), §F.2; source.pdf SHA256 2199cc2ec4c0cc01bfa75380982fe283d38a544dcae40abe5a37198f1a088114

import Definitions.Def_CliffordCert_Optimal_Supplement_support_model
import Definitions.Def_CliffordCert_Optimal_spectral_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal.Supplement
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq. (7): Nat.clog is the ceiling logarithm, so this works for every integer rank. -/
def supportQubits (k : ℕ) : ℕ := Nat.clog 2 k
def paddedDimension (k : ℕ) : ℕ := 2 ^ supportQubits k
def supportMessageQubits (q k : ℕ) : ℕ := min q (supportQubits k)
def supportMessageDimension (q k : ℕ) : ℕ := min (2 ^ q) (paddedDimension k)

def rankRate (q k : ℕ) (ε : ℝ) : ℝ :=
  (k : ℝ)^3 / ((min (2^q) k : ℕ)^2 * ε^2)

def leakageCopies (ε : ℝ) : ℕ := ⌈64 * Real.log 3 / ε^2⌉₊
def supportCopies (k : ℕ) (ε : ℝ) : ℕ := blockSize (supportQubits k) (ε / 2)

/-- The two computational codewords of the leakage message (distinct for q ≥ 1). -/
def zeroWord (q : ℕ) : Bits q := fun _ => 0
def oneWord (q : ℕ) : Bits q := fun j => if j.val = 0 then 1 else 0

/-- Eq. (33), embedded into the permitted r-dimensional quantum message. -/
def leakageChannel {n : ℕ} (q : ℕ) (P : Mat (Bits n)) :
    Mat (Bits n) →ₗ[ℂ] Mat (Bits q) :=
  fromCoefficients fun u v a b =>
    (if u = zeroWord q ∧ v = zeroWord q then P b a else 0) +
    (if u = oneWord q ∧ v = oneWord q then (1 - P) b a else 0)

/-- Eq. (34), followed by an isometric embedding of the R-dimensional message into r.
    J and A are respectively the support coordinates and the k-to-K isometry.
    B is an R-to-r isometry. Physical validity is not assumed by this definition. -/
def supportEncoder {n q k : ℕ} (σ : Mat (Bits n)) (J : Matrix (Bits n) (Fin k) ℂ)
    (A : Matrix (Bits (supportQubits k)) (Fin k) ℂ)
    (B : Matrix (Bits q) (Bits (supportMessageQubits q k)) ℂ)
    (C : EncoderFamily (supportQubits k) (supportMessageQubits q k)) (i : Fin C.length) :
    Mat (Bits n) →ₗ[ℂ] Mat (Bits q) :=
  (conjugation B).comp ((compression (Nat.min_le_right q (supportQubits k)) (C.unitary i)).comp
    ((conjugation A).comp (supportChannel σ J)))

/-- Leakage senders first, then the support blocks; the schedule is fixed before the input. -/
def rankSchedule {n q k : ℕ} (σ : Mat (Bits n)) (J : Matrix (Bits n) (Fin k) ℂ)
    (A : Matrix (Bits (supportQubits k)) (Fin k) ℂ)
    (B : Matrix (Bits q) (Bits (supportMessageQubits q k)) ℂ)
    (C : EncoderFamily (supportQubits k) (supportMessageQubits q k)) (ε : ℝ)
    (j : Fin (leakageCopies ε + C.length * supportCopies k ε)) :
    Mat (Bits n) →ₗ[ℂ] Mat (Bits q) :=
  if h : j.val < leakageCopies ε then leakageChannel q (supportProjection J)
  else if hs : 0 < supportCopies k ε then
    supportEncoder σ J A B C ⟨(j.val - leakageCopies ε) / supportCopies k ε,
      (Nat.div_lt_iff_lt_mul hs).mpr (by omega)⟩
  else 0

/-- Tensor isometric inclusion of the small messages; matrix product order is unchanged. -/
def messageInclusion {q a N : ℕ} (B : Matrix (Bits q) (Bits a) ℂ) :
    Matrix (Fin N → Bits q) (Fin N → Bits a) ℂ :=
  fun x y => ∏ j, B (x j) (y j)

/-- Eqs. (36)–(37): all leakage outcomes must be zero, and the existing block effect
    accepts exactly when the reported average is < ε²/(8 R L).
    This is an operator, without a bundled assumption of validity or success. -/
def rankEffect {n q k : ℕ} (σ : Mat (Bits n)) (J : Matrix (Bits n) (Fin k) ℂ)
    (A : Matrix (Bits (supportQubits k)) (Fin k) ℂ)
    (B : Matrix (Bits q) (Bits (supportMessageQubits q k)) ℂ)
    (C : EncoderFamily (supportQubits k) (supportMessageQubits q k)) (ε : ℝ) :
    Mat (Fin (leakageCopies ε + C.length * supportCopies k ε) → Bits q) :=
  let E : Mat (Fin (C.length * supportCopies k ε) → Bits (supportMessageQubits q k)) :=
    blockEffect (Nat.min_le_right q (supportQubits k)) C
    (conjugation A (supportReference σ J)) (ε / 2)
  let V : Matrix (Fin (C.length * supportCopies k ε) → Bits q)
      (Fin (C.length * supportCopies k ε) → Bits (supportMessageQubits q k)) ℂ :=
    messageInclusion B
  let H := V * E * Vᴴ
  fun x y =>
    (∏ j : Fin (leakageCopies ε),
      if x ⟨j.val, by omega⟩ = zeroWord q ∧ y ⟨j.val, by omega⟩ = zeroWord q then 1 else 0) *
    H (fun j => x ⟨leakageCopies ε + j.val, by omega⟩)
      (fun j => y ⟨leakageCopies ε + j.val, by omega⟩)

/-- A finite list covers the fixed schedule; repetitions in the list are harmless. -/
def CoversSchedule {n q m : ℕ} (π : Protocol (Bits n) (Bits q) m)
    (settings : List (Mat (Bits n) →ₗ[ℂ] Mat (Bits q))) : Prop :=
  (∀ Φ ∈ settings, WildeQIT.EntBreaking.IsQuantumChannel Φ) ∧
  ∀ j, π.encoder j ∈ settings

end CliffordCert.Optimal.Supplement


