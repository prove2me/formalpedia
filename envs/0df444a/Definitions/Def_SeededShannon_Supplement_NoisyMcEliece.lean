-- Prove2me | Definitions.Def_SeededShannon_Supplement_NoisyMcEliece
-- name    : SeededShannon_Supplement_NoisyMcEliece
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:42:38.457776+00:00
-- url     : https://prove2.me/theorems/55896cc3-022b-447f-874f-a6963f2bca97
-- title:
--   Binary linear code families and the Noisy McEliece assumption (Assumption B.1)
-- statement:
--   An **efficiently samplable family of binary linear codes of dimension $k$** is a polynomial-time sampler $\kappa\leftarrow\mathrm{Samp}(1^\lambda)$ with a polynomial-time map $\kappa\mapsto G_\kappa\in\mathbb F_2^{m\times k}$, every $G_\kappa$ of full column rank $k$. A **deterministic polynomial-time list decoder at radius $a$** returns, on $(\kappa,v)$, a list containing every $u$ with $\delta(v,G_\kappa u)\le a$.
--
--   Write $B_\theta(\mathbb F_2^n)=\{z:\mathrm{wt}(z)\le\lfloor\theta n\rfloor\}$. The **binary Noisy McEliece assumption** for the family, seed dimension $w$ ($m\ge k\ge 2w$), public-key noise rate $\mu$ and ciphertext noise rate $\eta$ states
--   $$(A,\ A_1 s+e)\ \stackrel{c}{\approx}\ (A,\ u_{\mathrm{unif}}),$$
--   where $A=P\cdot G_\kappa\cdot T+E=(A_1\mid A_2)$ with $\kappa$ sampled, $P$ a uniform $m\times m$ permutation matrix, $T\in\mathbb F_2^{k\times 2w}$ uniform of full column rank, $E\in\mathbb F_2^{m\times 2w}$ with independent Bernoulli-$\mu$ entries, $s\leftarrow B_\mu(\mathbb F_2^w)$ and $e\leftarrow B_\eta(\mathbb F_2^m)$ uniform, and $u_{\mathrm{unif}}\leftarrow\mathbb F_2^m$ uniform: every efficient nonuniform distinguisher has negligible advantage.
--
--   This is the hardness assumption behind the strongly robust PRCs of Theorem 3.6.
--
--   **Formalization Note** The noise rate $\mu$ is dyadic, $\mu=\mu_{\mathrm{num}}/2^{\mu_{\mathrm{exp}}}$ (the source fixes finite binary representations), and each Bernoulli entry is sampled exactly from $\mu_{\mathrm{exp}}$ coins. The assumption is the published computational closeness `NoisyOWMPC.CompClose` with error $0$, and is a hypothesis, not an axiom.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Assumption B.1, p.62 (PDF p.65); Theorem 3.6, p.18; Construction B.2, p.63

import Mathlib
import Definitions.Def_NoisyOWMPC_CompClose
import Definitions.Def_NoisyOWMPC_wprob

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC

/-- The bit string of a vector over `𝔽₂ = ZMod 2`. -/
def vecBits {n : ℕ} (v : Fin n → ZMod 2) : List Bool := List.ofFn (fun i => decide (v i = 1))

/-- The bit string of a matrix over `𝔽₂`, row by row. -/
def matBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : List Bool :=
  (List.ofFn (fun i => vecBits (A i))).flatten

/-- The Hamming weight of a vector over `𝔽₂`. -/
def wt2 {n : ℕ} (v : Fin n → ZMod 2) : ℕ := (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- The ball `B_θ(𝔽₂^n) = {z ∈ 𝔽₂^n : wt(z) ≤ ⌊θ · n⌋}` (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Appendix B, p.62), as a type. -/
abbrev Ball2 (n : ℕ) (θ : ℝ) : Type := {z : Fin n → ZMod 2 // wt2 z ≤ ⌊θ * n⌋₊}

/-- An **efficiently samplable family of binary linear codes** `{C_κ ⊆ 𝔽₂^m}` of dimension `k`
with generators `G_κ ∈ 𝔽₂^{m×k}` (Theorem 3.6, p.18; Assumption B.1, p.62): `κ ← Samp(1^λ; r)` and
the generator `G_κ`. -/
structure LinCodeFamily where
  /-- the length `m(λ)` -/
  m : ℕ → ℕ
  /-- the dimension `k(λ)` -/
  k : ℕ → ℕ
  /-- coins of the sampler -/
  coins : ℕ → ℕ
  /-- `κ ← Samp(1^λ; r)` -/
  samp : (lam : ℕ) → (Fin (coins lam) → Bool) → List Bool
  /-- the generator `G_κ` -/
  gen : (lam : ℕ) → List Bool → Matrix (Fin (m lam)) (Fin (k lam)) (ZMod 2)

/-- The family is **efficiently samplable of dimension `k`**: polynomially many coins, a
polynomial-time sampler, a polynomial-time map `κ ↦ G_κ`, and every sampled generator has full
column rank `k`. -/
def LinCodeFamily.IsSamplable (F : LinCodeFamily) : Prop :=
  PolyBounded F.coins ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (F.coins lam) → Bool)) (fun i => [unary i.1, bits i.2])
    (fun i => F.samp i.1 i.2) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (F.coins lam) → Bool)) (fun i => [unary i.1, F.samp i.1 i.2])
    (fun i => matBits (F.gen i.1 (F.samp i.1 i.2))) ∧
  ∀ lam (r : Fin (F.coins lam) → Bool), (F.gen lam (F.samp lam r)).rank = F.k lam

/-- `ListDec` is a **deterministic polynomial-time list decoder at radius `a`** (Theorem 3.6, p.18;
Construction B.2, p.63: "`ListDec_κ(v)` return[s] a polynomial-size list containing every message `u`
with `δ(v, G_κ · u) ≤ a`"): one polynomial-time machine computes `ListDec_κ(v)` from `(1^λ, κ, v)`
for sampled `κ`, and the list contains every `u` with `Δ(v, G_κ u) ≤ a · m`. -/
def LinCodeFamily.IsListDecoder (F : LinCodeFamily) (a : ℝ)
    (dec : (lam : ℕ) → List Bool → (Fin (F.m lam) → ZMod 2) → List (Fin (F.k lam) → ZMod 2)) :
    Prop :=
  PolyTimeOn (ι := (lam : ℕ) × (Fin (F.coins lam) → Bool) × (Fin (F.m lam) → ZMod 2))
    (fun i => [unary i.1, F.samp i.1 i.2.1, vecBits i.2.2])
    (fun i => QAdvFew.PoQOracle.tup ((dec i.1 (F.samp i.1 i.2.1) i.2.2).map vecBits)) ∧
  ∀ lam (r : Fin (F.coins lam) → Bool) (v : Fin (F.m lam) → ZMod 2) (u : Fin (F.k lam) → ZMod 2),
    (hammingDist v ((F.gen lam (F.samp lam r)).mulVec u) : ℝ) ≤ a * F.m lam →
      u ∈ dec lam (F.samp lam r) v

/-- The dyadic noise rate `μ(λ) = μnum(λ)/2^{μexp(λ)}` (p.62: "Public-key noise rates have finite
binary representations, allowing exact Bernoulli sampling"). -/
noncomputable def dyadic (num ex : ℕ → ℕ) (lam : ℕ) : ℝ := (num lam : ℝ) / 2 ^ ex lam

/-- An exact Bernoulli-`(j/2^e)` bit from `e` uniform coins: `1` iff the coins, read as a binary
number, are below `j`. -/
def bern (j e : ℕ) (c : Fin e → Bool) : ZMod 2 :=
  if (∑ i : Fin e, if c i then 2 ^ i.val else 0) < j then 1 else 0

/-- The public-matrix randomness of `Exp_NM` (Assumption B.1, step 1): the code coins, a uniform
permutation of the `m` coordinates, a uniform full-column-rank `T ∈ 𝔽₂^{k×2w}` and the coins of the
Bernoulli-`μ` entries of `E ∈ 𝔽₂^{m×2w}`. -/
abbrev NMPub (F : LinCodeFamily) (w μexp : ℕ → ℕ) (lam : ℕ) : Type :=
  (Fin (F.coins lam) → Bool) × Equiv.Perm (Fin (F.m lam)) ×
    {T : Matrix (Fin (F.k lam)) (Fin (w lam + w lam)) (ZMod 2) // T.rank = w lam + w lam} ×
    (Fin (F.m lam) → Fin (w lam + w lam) → Fin (μexp lam) → Bool)

/-- The public matrix `A = P · G_κ · T + E = (A₁ | A₂)` (Assumption B.1, step 1). -/
noncomputable def NMPub.mat {F : LinCodeFamily} {w μexp : ℕ → ℕ} (μnum : ℕ → ℕ) {lam : ℕ}
    (ω : NMPub F w μexp lam) : Matrix (Fin (F.m lam)) (Fin (w lam + w lam)) (ZMod 2) :=
  fun i j => (F.gen lam (F.samp lam ω.1) * ω.2.2.1.1) (ω.2.1 i) j +
    bern (μnum lam) (μexp lam) (ω.2.2.2 i j)

open Classical in
/-- **Assumption B.1 (binary Noisy McEliece)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Assumption B.1, p.62) for the family `F`, seed dimension `w`,
public-key noise rate `μ = μnum/2^{μexp}` and ciphertext noise rate `η`:
`(A, A₁ · s + e) ≈^c (A, u_unif)` (B.1), where `A = P · G_κ · T + E = (A₁ | A₂)` with `κ` sampled,
`P` a uniform permutation matrix on `m` coordinates, `T ∈ 𝔽₂^{k×2w}` uniform of full column rank,
`E ∈ 𝔽₂^{m×2w}` with independent Bernoulli-`μ` entries, `s ← B_μ(𝔽₂^w)`, `e ← B_η(𝔽₂^m)` uniform, and
`u_unif ← 𝔽₂^m` uniform: every nonuniform polynomial-size distinguisher has negligible advantage
`Δ_NM(A, λ) = |Pr[Exp^{(0)}_NM(A, λ) = 1] − Pr[Exp^{(1)}_NM(A, λ) = 1]|`.

**Formalization Note** This is the published `NoisyOWMPC.CompClose` with error `0`; the
distinguisher receives the tuple encoding of `(A, z)`. `P · M` is the row reindexing `M ∘ π` by a
uniform permutation `π` (the law of `P · M` is the same for either convention). `A₁` is the first
`w` columns. The Bernoulli entries are sampled exactly from `μexp` coins each. The assumption is a
hypothesis on the given family and parameters, not an axiom. -/
def NoisyMcEliece (F : LinCodeFamily) (w μnum μexp : ℕ → ℕ) (η : ℝ) : Prop :=
  CompClose (I := fun _ => Unit)
    (Ω₀ := fun lam => NMPub F w μexp lam × Ball2 (w lam) (dyadic μnum μexp lam) ×
      Ball2 (F.m lam) η)
    (Ω₁ := fun lam => NMPub F w μexp lam × (Fin (F.m lam) → ZMod 2))
    (fun _ _ => unifW _)
    (fun lam _ ω =>
      let A := ω.1.mat μnum
      QAdvFew.PoQOracle.tup [matBits A,
        vecBits (Matrix.mulVec (Matrix.of fun i j => A i (Fin.castAdd (w lam) j)) ω.2.1.1 +
          ω.2.2.1)])
    (fun _ _ => unifW _)
    (fun lam _ ω => QAdvFew.PoQOracle.tup [matBits (ω.1.mat μnum), vecBits ω.2])
    (fun _ => 0)

end SeededShannon.Supplement


