-- Prove2me | Definitions.Def_RegevLWE_Correctness_Cryptosystem
-- name    : RegevLWE_Correctness_Cryptosystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:54.947246+00:00
-- url     : https://prove2.me/theorems/eb579dba-8922-4de8-92cf-994486fd19fc
-- title:
--   §5, p. 34:35 — Regev's public-key cryptosystem over ℤ_p as a probability experiment; |a| and χ^⋆k
-- statement:
--   Fix an integer $p \ge 2$ and write $\mathbb Z_p = \{0, 1, \dots, p-1\}$ with addition modulo $p$ (p. 34:14). Fix integers $n, m \ge 0$ and a probability distribution $\chi$ on $\mathbb Z_p$. All additions below are in $\mathbb Z_p$.
--
--   1. **Distance from 0.** For $a \in \mathbb Z_p$, $|a|$ is the integer $a$ if $a \in \{0, 1, \dots, \lfloor p/2 \rfloor\}$ and the integer $p - a$ otherwise; it is the distance of $a$ from $0$ modulo $p$.
--   2. **Convolution powers.** For $k \ge 0$, $\chi^{\star k}$ is the distribution of the sum of $k$ independent samples from $\chi$; $\chi^{\star 0}$ is the point mass at $0$.
--   3. **Keys.** The private key is $s \in \mathbb Z_p^n$. Given $a_1, \dots, a_m \in \mathbb Z_p^n$ and $e_1, \dots, e_m \in \mathbb Z_p$, the public key is $(a_i, b_i)_{i=1}^m$ with
--   $$b_i = \langle a_i, s\rangle + e_i .$$
--   4. **Encryption.** For a subset $S \subseteq [m]$, the encryption of the bit $0$ is $\bigl(\sum_{i\in S} a_i, \sum_{i\in S} b_i\bigr)$ and the encryption of the bit $1$ is $\bigl(\sum_{i\in S} a_i, \lfloor p/2\rfloor + \sum_{i\in S} b_i\bigr)$.
--   5. **Decryption.** The decryption of a pair $(a, b)$ is $0$ if $b - \langle a, s\rangle$ is closer to $0$ than to $\lfloor p/2 \rfloor$ modulo $p$, that is, if $|b - \langle a, s\rangle| < |b - \langle a, s\rangle - \lfloor p/2\rfloor|$, and $1$ otherwise.
--   6. **The protocol as an experiment.** For a bit $c$, choose $s$ uniformly in $\mathbb Z_p^n$, $a_1, \dots, a_m$ independently and uniformly in $\mathbb Z_p^n$, $e_1, \dots, e_m$ independently according to $\chi$, and $S$ uniformly among all $2^m$ subsets of $[m]$; encrypt $c$ under the public key and decrypt with $s$. The **outcome distribution** is the law of the decrypted bit.
--
--   This is the public-key cryptosystem of Section 5, whose security rests on the hardness of learning with errors; Lemma 5.1 bounds its decryption error.
--
--   **Formalization Note** `absZ a` is $|a|$ computed from the representative `a.val` $\in\{0,\dots,p-1\}$, with `p / 2` the natural-number floor $\lfloor p/2\rfloor$. `convPow χ k` is $\chi^{\star k}$ as a `PMF`, defined by $\chi^{\star 0} = \delta_0$ and $\chi^{\star(k+1)}$ = law of $x + y$ with $x \sim \chi^{\star k}$, $y \sim \chi$ independent. `iidPMF χ m` is the product distribution on $\mathbb Z_p^m$ with mass $\prod_i \chi(e_i)$. Bits are `Fin 2`. `decodeResidue x` is the decision rule applied to the residue $x = b - \langle a, s\rangle$ (ties go to $1$, as printed: "otherwise, the decryption is 1"). `outcome n m χ c` is the experiment of item 6 as a `PMF (Fin 2)`, built from uniform distributions and binds. Only `[NeZero p]` is needed for the definitions; the hypothesis $p \ge 2$ is carried by the theorems.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:35, §5 (Private key, Public Key, Encryption, Decryption; definitions of χ^⋆k and |a|); p. 34:14 (ℤ_p for p ≥ 2)

import Mathlib

namespace RegevLWE.Correctness

open Matrix

variable {p : ℕ} [NeZero p]

/-- `|a|` for `a ∈ ℤ_p` (Regev, J. ACM 2009, p. 34:35): the integer `a` if
`a ∈ {0, 1, …, ⌊p/2⌋}`, and the integer `p − a` otherwise. It is the distance of `a` from `0`
modulo `p`. Here `a.val ∈ {0, …, p − 1}` is the representative of `a`, and `p / 2` is `⌊p/2⌋`. -/
def absZ (a : ZMod p) : ℕ :=
  if a.val ≤ p / 2 then a.val else p - a.val

/-- `χ^⋆k` (p. 34:35): the distribution on `ℤ_p` of the sum of `k` independent samples from `χ`,
with addition in `ℤ_p`; `χ^⋆0` is the point mass at `0`. -/
noncomputable def convPow (χ : PMF (ZMod p)) : ℕ → PMF (ZMod p)
  | 0 => PMF.pure 0
  | k + 1 => (convPow χ k).bind fun x => χ.map fun y => x + y

/-- The distribution of `(e₁, …, e_m) ∈ ℤ_p^m` with `e₁, …, e_m` chosen independently according
to `χ`: the mass of `e` is `∏ᵢ χ(eᵢ)`. -/
noncomputable def iidPMF (χ : PMF (ZMod p)) (m : ℕ) : PMF (Fin m → ZMod p) :=
  PMF.ofFintype (fun e => ∏ i, χ (e i)) (by
    rw [← Fintype.prod_sum (fun (_ : Fin m) (x : ZMod p) => χ x)]
    have h : ∑ x : ZMod p, χ x = 1 := by
      rw [← tsum_fintype (L := SummationFilter.unconditional (ZMod p))]; exact χ.tsum_coe
    simp [h])

/-- The public key `(aᵢ, bᵢ)_{i=1}^m` with `bᵢ = ⟨aᵢ, s⟩ + eᵢ` (p. 34:35), for vectors
`a₁, …, a_m ∈ ℤ_pⁿ`, private key `s ∈ ℤ_pⁿ` and errors `e₁, …, e_m ∈ ℤ_p`. -/
def publicKey {n m : ℕ} (a : Fin m → Fin n → ZMod p) (s : Fin n → ZMod p) (e : Fin m → ZMod p) :
    Fin m → (Fin n → ZMod p) × ZMod p :=
  fun i => (a i, a i ⬝ᵥ s + e i)

/-- Encryption of a bit `c ∈ {0, 1}` with the subset `S ⊆ [m]` (p. 34:35):
`(∑_{i∈S} aᵢ, ∑_{i∈S} bᵢ)` if the bit is `0`, and `(∑_{i∈S} aᵢ, ⌊p/2⌋ + ∑_{i∈S} bᵢ)` if the bit
is `1`. -/
def encrypt {n m : ℕ} (pk : Fin m → (Fin n → ZMod p) × ZMod p) (c : Fin 2) (S : Finset (Fin m)) :
    (Fin n → ZMod p) × ZMod p :=
  (∑ i ∈ S, (pk i).1,
    (if c = 1 then (((p / 2 : ℕ) : ZMod p)) else 0) + ∑ i ∈ S, (pk i).2)

/-- The decision rule of decryption applied to the residue `x = b − ⟨a, s⟩`: `0` if `x` is
closer to `0` than to `⌊p/2⌋` modulo `p`, i.e. `|x| < |x − ⌊p/2⌋|`, and `1` otherwise
(ties decrypt to `1`). -/
def decodeResidue (x : ZMod p) : Fin 2 :=
  if absZ x < absZ (x - ((p / 2 : ℕ) : ZMod p)) then 0 else 1

/-- Decryption of a pair `(a, b)` with private key `s` (p. 34:35): `0` if `b − ⟨a, s⟩` is closer
to `0` than to `⌊p/2⌋` modulo `p`, and `1` otherwise. -/
def decrypt {n : ℕ} (s : Fin n → ZMod p) (ct : (Fin n → ZMod p) × ZMod p) : Fin 2 :=
  decodeResidue (ct.2 - ct.1 ⬝ᵥ s)

/-- The whole protocol for a bit `c`, as the distribution of its outcome (p. 34:35): choose the
private key `s ∈ ℤ_pⁿ` uniformly, `a₁, …, a_m ∈ ℤ_pⁿ` independently and uniformly, `e₁, …, e_m`
independently according to `χ`, form the public key, choose `S` uniformly among all `2^m`
subsets of `[m]`, encrypt `c`, and decrypt the result. -/
noncomputable def outcome (n m : ℕ) (χ : PMF (ZMod p)) (c : Fin 2) : PMF (Fin 2) :=
  (PMF.uniformOfFintype (Fin n → ZMod p)).bind fun s =>
  (PMF.uniformOfFintype (Fin m → Fin n → ZMod p)).bind fun a =>
  (iidPMF χ m).bind fun e =>
  (PMF.uniformOfFintype (Finset (Fin m))).map fun S =>
    decrypt s (encrypt (publicKey a s e) c S)

end RegevLWE.Correctness


