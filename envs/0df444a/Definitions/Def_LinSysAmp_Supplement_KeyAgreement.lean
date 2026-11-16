-- Prove2me | Definitions.Def_LinSysAmp_Supplement_KeyAgreement
-- name    : LinSysAmp_Supplement_KeyAgreement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:48:56.886202+00:00
-- url     : https://prove2.me/theorems/b2620f9e-ff91-4b24-9b5a-6cf8877f5b0c
-- title:
--   The key-agreement protocol: ideal distribution, key recovery, bit extraction, random rank (§8)
-- statement:
--   Let $\mathbb F_q$ be a finite field. In the protocol of Figure 10, Alice sends $(M,r)$ with $r=a^\top M$ and Bob sends $y=Mb$; the transcript is $\tau=(M,r,y)$ and the key is $K=a^\top Mb$. On the **ideal distribution** (p.46) $M\leftarrow GL_n(\mathbb F_q)$, $r\leftarrow\mathbb F_q^{1\times n}$ and $y\leftarrow\mathbb F_q^n$ are independent and uniform, and $K=rM^{-1}y$.
--
--   1. A **key-recovery algorithm** of dimension $c$ is a randomized map from transcripts $(M,r,y)$ to $\mathbb F_q$; it **recovers the key with probability $\alpha$ on the ideal distribution** if $\Pr_{M,r,y,P}[P(M,r,y)=rM^{-1}y]\ge\alpha$.
--   2. **Bit extraction** (p.47): for $q=2^\ell$, fix an $\mathbb F_2$-linear bijection $\mathrm{enc}:\mathbb F_q\to\{0,1\}^\ell$; a seed $s\leftarrow\{0,1\}^\ell\setminus\{0\}$ is sampled and the bit is $\langle s,\mathrm{enc}(K)\rangle$ over $\mathbb F_2$.
--   3. A **distinguisher** $D$ maps $(\tau,s,b)$ to a random bit; its **advantage** on the ideal distribution is
--   $$\Pr[D(\tau,s,\langle s,\mathrm{enc}(K)\rangle)=1]-\Pr[D(\tau,s,u)=1],$$
--   with $s$ uniform nonzero and $u\leftarrow\{0,1\}$ independent.
--   4. $\mathbb E_{A}[\cdot]$ over "a uniformly random matrix of rank $\rho$ in $\mathbb F_q^{N\times N}$" (Definition 8.7) is the average over the $N\times N$ matrices of rank exactly $\rho$.
--
--   The module also gives the oracle-machine interfaces: a distinguisher call reads $M$, $r$, $y$, the $\ell$ bits of $s$ and the bit $b$ and writes a bit; a key-recovery call takes the dimension $c$ from the mode and calls $P_c$. These objects are used by Theorems 8.6 and 8.10.
--
--   **Formalization Note** Row vectors are functions $\mathrm{Fin}\,n\to F$ and $rM^{-1}y$ is a dot product. An $\mathbb F_2$-linear bijection is an additive equivalence $F\simeq_+(\mathrm{Fin}\,\ell\to\mathbb Z/2)$. In machine memory a bit is the field element $0$ or $1$, and a cell is read as the bit $0$ if it is $0$ and $1$ otherwise.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), §8.1, pp.46–47 (PDF pp.48–49); Figure 10, p.47 (PDF p.49); Definition 8.7, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_LinSysAmp_lineqSuccess
import Definitions.Def_LinSysAmp_Supplement_OracleMachine

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

/-!
# The key-agreement protocol: ideal distribution, key recovery, bit extraction, random rank

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), §8.1–8.3,
pp.46–50 (PDF pp.48–52).

* Figure 10 (p.47): Alice sends `(M, r)` with `r = a⊤M`, Bob sends `y = Mb`, the key is
  `K = a⊤Mb`; "The transcript is τ = (M, r, y)."
* The ideal distribution (p.46): "M ← GL_n(F_q), r ← F_q^{1×n}, and y ← F_qⁿ are independent and
  uniform, and K = rM⁻¹y."
* Bit extraction (p.47): "For q = 2^ℓ, fix an F₂-linear bijection enc : F_q → {0, 1}^ℓ […]. Alice
  samples s ← {0, 1}^ℓ \ {0} […]. Both parties output ⟨s, enc(K)⟩, with the inner product taken
  over F₂."
* Definition 8.7 (p.50): "let A be a uniformly random matrix of rank ρ in F_q^{N×N}."

**Formalization Note.**
* Row vectors `r ∈ F^{1×n}` are functions `Fin n → F`, and `rM⁻¹y` is `r ⬝ᵥ (M⁻¹ *ᵥ y)`.
* A **key-recovery algorithm** of dimension `c` is a randomized map from a transcript `(M, r, y)` to
  a distribution on `F`; "recovers the key with probability `α` on the ideal distribution" is
  `α ≤ keySuccess P`. It is defined on every transcript; only its behaviour on the ideal
  distribution enters the hypothesis.
* `{0,1}^ℓ` is `Fin ℓ → ZMod 2`, bits are `ZMod 2`, and an `F₂`-linear bijection
  `enc : F → {0,1}^ℓ` is an additive equivalence `F ≃+ (Fin ℓ → ZMod 2)` (every additive map
  between `F₂`-vector spaces is `F₂`-linear).
* A **distinguisher** is a randomized map from `(M, r, y, s, b)` to a bit. Its advantage is
  `Pr[D(τ, s, ⟨s, enc(K)⟩) = 1] − Pr[D(τ, s, u) = 1]`, on the ideal distribution, with `s` uniform
  in `{0,1}^ℓ \ {0}` and `u ← {0, 1}` independent.
* Machine interfaces: `distIface` reads `n² + 2n + ℓ + 1` cells (`M` row-major, `r`, `y`, the `ℓ`
  bits of `s`, the bit `b`); a cell is read as the bit `0` if it is `0` and `1` otherwise; the
  answer bit is written as `0` or `1` of `F`. `keyIface` takes the dimension `c` from the mode,
  reads `c² + 2c` cells (`M`, `r`, `y`) and calls `P_c`, writing the key.
* `rankAvg N ρ f` is the average of `f` over the `N × N` matrices of rank exactly `ρ`.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The key of a transcript on the ideal distribution, `K = rM⁻¹y`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §8.1, p.46 (PDF p.48).) -/
noncomputable def idealKey {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (r y : Fin n → F) : F :=
  r ⬝ᵥ (M⁻¹ *ᵥ y)

/-- A key-recovery algorithm of dimension `c`: transcript `(M, r, y)` ↦ distribution on keys.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 8.1, §8.1, p.46 (PDF p.48).) -/
abbrev KeyRec (c : ℕ) (F : Type*) :=
  Matrix (Fin c) (Fin c) F → (Fin c → F) → (Fin c → F) → PMF F

/-- `Pr_{M ← GL_c(F), r, y, P}[P(M, r, y) = rM⁻¹y]`: key recovery on the ideal distribution.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §8.1, p.46 (PDF p.48).) -/
noncomputable def keySuccess {c : ℕ} (P : KeyRec c F) : ℝ :=
  ((Fintype.card (LinSysAmp.InvMat c F) : ℝ) * (Fintype.card F : ℝ) ^ c * (Fintype.card F : ℝ) ^ c)⁻¹ *
    ∑ M : LinSysAmp.InvMat c F, ∑ r : Fin c → F, ∑ y : Fin c → F,
      (P M.1 r y (idealKey M.1 r y)).toReal

/-- The inner product `⟨s, z⟩` over `F₂` of two strings of `{0,1}^ℓ`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §8.1, p.47 (PDF p.49).) -/
def bitInner {ℓ : ℕ} (s z : Fin ℓ → ZMod 2) : ZMod 2 := ∑ i, s i * z i

/-- A distinguisher for the extracted bit: `(M, r, y, s, b)` ↦ distribution on bits.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §8.1–8.2, pp.46–49.) -/
abbrev Distinguisher (n ℓ : ℕ) (F : Type*) :=
  Matrix (Fin n) (Fin n) F → (Fin n → F) → (Fin n → F) → (Fin ℓ → ZMod 2) → ZMod 2 → PMF (ZMod 2)

/-- The advantage of `D` on the ideal distribution:
`Pr[D(τ, s, ⟨s, enc(K)⟩) = 1] − Pr[D(τ, s, u) = 1]`, with `M ← GL_n(F)`, `r, y ← Fⁿ`,
`s ← {0,1}^ℓ \ {0}`, `u ← {0,1}`, all independent.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §8.1, p.47, Theorem 8.6, p.49.) -/
noncomputable def distAdvantage {n ℓ : ℕ} (enc : F ≃+ (Fin ℓ → ZMod 2)) (D : Distinguisher n ℓ F) :
    ℝ :=
  ((Fintype.card (LinSysAmp.InvMat n F) : ℝ) * (Fintype.card F : ℝ) ^ n * (Fintype.card F : ℝ) ^ n *
      ((2 : ℝ) ^ ℓ - 1))⁻¹ *
    ∑ M : LinSysAmp.InvMat n F, ∑ r : Fin n → F, ∑ y : Fin n → F,
      ∑ s ∈ Finset.univ.filter (fun s : Fin ℓ → ZMod 2 => s ≠ 0),
        ((D M.1 r y s (bitInner s (enc (idealKey M.1 r y))) 1).toReal -
          (1 / 2 : ℝ) * ∑ u : ZMod 2, (D M.1 r y s u 1).toReal)

/-- A field cell read as a bit: `0` if the cell is `0`, else `1`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §8.1, p.47 (PDF p.49).) -/
def cellBit (x : F) : ZMod 2 := if x = 0 then 0 else 1

/-- A bit written as the field element `0` or `1`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §8.1, p.47 (PDF p.49).) -/
def bitCell (b : ZMod 2) : F := if b = 0 then 0 else 1

/-- The machine interface of a distinguisher: a call reads `M` (row-major), `r`, `y`, the `ℓ` bits of
`s` and the bit `b`, and writes the answer bit.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §8.2, p.49 (PDF p.51).) -/
noncomputable def distIface {n ℓ : ℕ} (D : Distinguisher n ℓ F) : Iface F Unit where
  inLen _ := n * n + n + n + ℓ + 1
  call _ x _ :=
    (D (unflatMat n x 0) (unflatVec n x (n * n)) (unflatVec n x (n * n + n))
        (fun i => cellBit (x.getD (n * n + n + n + i) 0)) (cellBit (x.getD (n * n + n + n + ℓ) 0))).map
      fun b => ([bitCell b], none)

/-- The machine interface of a family of key-recovery algorithms `(P_c)_c`: in mode `c` a call reads
a transcript of dimension `c` (`M` row-major, `r`, `y`) and writes the answer of `P_c`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Theorem 8.10, p.51 (PDF p.53).) -/
noncomputable def keyIface (P : (c : ℕ) → KeyRec c F) : Iface F Unit where
  inLen c := c * c + c + c
  call c x _ :=
    (P c (unflatMat c x 0) (unflatVec c x (c * c)) (unflatVec c x (c * c + c))).map
      fun K => ([K], none)

open Classical in
/-- The average of `f` over the `N × N` matrices of rank exactly `ρ` (uniform distribution of
Definition 8.7). (arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 8.7, p.50.) -/
noncomputable def rankAvg (N ρ : ℕ) (f : Matrix (Fin N) (Fin N) F → ℝ) : ℝ :=
  ((Finset.univ.filter fun A : Matrix (Fin N) (Fin N) F => A.rank = ρ).card : ℝ)⁻¹ *
    ∑ A ∈ Finset.univ.filter (fun A : Matrix (Fin N) (Fin N) F => A.rank = ρ), f A

end LinSysAmp.Supplement


