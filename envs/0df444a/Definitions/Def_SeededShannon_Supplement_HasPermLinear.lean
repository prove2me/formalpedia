-- Prove2me | Definitions.Def_SeededShannon_Supplement_HasPermLinear
-- name    : SeededShannon_Supplement_HasPermLinear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:39:35.181624+00:00
-- url     : https://prove2.me/theorems/ad00a9d5-7900-481f-9044-99312f76b9ea
-- title:
--   Permuted-linear structure and pairwise column robustness (Definitions 7.2, 7.4)
-- statement:
--   Let $\Pi$ be a seeded code on messages of length $d=k+v$ with codeword length $N$, and $E:\mathbb F_2^k\times\mathbb F_2^v\to\mathbb F_2^N$ an injective binary-linear encoder.
--
--   1. **Permuted-linear structure (Definition 7.2).** $\Pi$ has $(\eta,\ell_{\mathrm{lab}})$-permuted-linear structure over $E$ if there are a label function $\mathrm{lab}_{\mathrm{crs}}(u)\in\{0,1\}^{\ell_{\mathrm{lab}}}$ and, for every seed and label $a$, a permutation $\pi_{\mathrm{crs},a}$ of $[N]$ and a mask $s_{\mathrm{crs},a}$, such that for every seed $\mathrm{crs}$ output by Setup and every $u=(x,z)$,
--   $$\Delta\big(\mathrm{Encode}(\mathrm{crs},u),\,a_{\mathrm{crs}}(u)\big)\le\eta N,\qquad a_{\mathrm{crs}}(u)=\pi_{\mathrm{crs},\mathrm{lab}_{\mathrm{crs}}(u)}\big(E(x,z)\big)\oplus s_{\mathrm{crs},\mathrm{lab}_{\mathrm{crs}}(u)}.$$
--   2. **Pairwise column robustness (Definition 7.4).** Write $E(x,z)=Ax+Bz$ and $w=\lceil\sqrt v\rceil$. $E$ is $Q$-pairwise column robust if for every pair of permutations $\pi_1,\pi_2$ of $[N]$, a uniform $w$-subset $S\subseteq[N]$ satisfies
--   $$\Pr_S\big[\mathrm{rank}(B_U)=|U|\big]\ge\frac1{Q},\qquad U=\pi_1^{-1}(S)\cup\pi_2^{-1}(S).$$
--
--   These are the structural hypotheses on the base code in Theorem 7.10.
--
--   **Formalization Note** The structure is required at every supported length $d=k+v(\lambda)$; $E$, the labels, permutations and masks are functions of $(\lambda,k)$ and the seed. Permutations act by $(\pi(w))_{\pi(a)}=w_a$. $\mathrm{rank}(B_U)=|U|$ is linear independence over $\mathbb F_2$ of the rows of $B$ indexed by $U$; $\Pr\ge 1/Q$ is written $\#\{\text{subsets}\}\le Q\cdot\#\{\text{good subsets}\}$.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definitions 7.2, 7.4, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_SeededShannon_SeededCode

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC SeededShannon

/-- An encoder `E : 𝔽₂^k × 𝔽₂^v → 𝔽₂^N` is **injective and binary-linear** (Definition 7.2, p.49):
`E(x ⊕ x′, z ⊕ z′) = E(x, z) ⊕ E(x′, z′)` and `E` is injective. -/
def IsInjLinear {k v N : ℕ} (E : (Fin k → Bool) → (Fin v → Bool) → Fin N → Bool) : Prop :=
  Function.Injective (fun u : (Fin k → Bool) × (Fin v → Bool) => E u.1 u.2) ∧
  ∀ (x x' : Fin k → Bool) (z z' : Fin v → Bool),
    E (fun i => xor (x i) (x' i)) (fun i => xor (z i) (z' i)) =
      fun j => xor (E x z j) (E x' z' j)

/-- A permutation `π` of `[N]` applied to a word, with the convention `(π(w))_{π(a)} = w_a`
(Fig. 6, p.39). -/
def permWord {N : ℕ} (π : Equiv.Perm (Fin N)) (w : Fin N → Bool) : Fin N → Bool :=
  fun j => w (π.symm j)

/-- **`(η, ℓ_lab)`-permuted-linear structure** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Definition 7.2, p.49) of a seeded code `Π` on message
lengths `d = k + v(λ)` over the injective binary-linear encoders `E_{λ,k} : 𝔽₂^k × 𝔽₂^{v(λ)} →
𝔽₂^{N(λ, d)}`: there are a label function `lab_crs(u) ∈ {0,1}^{ℓ_lab(λ)}`, and for every seed `crs`
and label `a` a permutation `π_{crs,a}` of `[N]` and a mask `s_{crs,a} ∈ {0,1}^N`, such that for every
seed `crs` output by Setup at a supported `(λ, d)` and every `u = (x, z) ∈ {0,1}^d`,
`Δ(Encode(crs, u), a_crs(u)) ≤ η · N` with the latent word
`a_crs(u) = π_{crs, lab_crs(u)}(E(x, z)) ⊕ s_{crs, lab_crs(u)}` (7.1).

**Formalization Note** The base code's supported lengths are `supp`; the structure is required at
every supported `d = k + v(λ)`. `E`, `lab`, `π` and `s` are given as functions of `(λ, k)` (and of the
seed). The message `u = (x, z)` is the bit string `x ‖ z`. -/
def HasPermLinear (C : SeededCode) (supp : ℕ → ℕ → Prop) (v : ℕ → ℕ) (η : ℝ) (lablen : ℕ → ℕ)
    (E : (lam k : ℕ) → (Fin k → Bool) → (Fin (v lam) → Bool) → Fin (C.N lam (k + v lam)) → Bool)
    (lab : (lam k : ℕ) → List Bool → (Fin k → Bool) → (Fin (v lam) → Bool) → Fin (lablen lam) → Bool)
    (π : (lam k : ℕ) → List Bool → (Fin (lablen lam) → Bool) →
      Equiv.Perm (Fin (C.N lam (k + v lam))))
    (s : (lam k : ℕ) → List Bool → (Fin (lablen lam) → Bool) → Fin (C.N lam (k + v lam)) → Bool) :
    Prop :=
  ∀ lam k, supp lam (k + v lam) → IsInjLinear (E lam k) ∧
    ∀ (r : Fin (C.setupCoins lam (k + v lam)) → Bool) (x : Fin k → Bool) (z : Fin (v lam) → Bool),
      let crs := C.setup lam (k + v lam) r
      let a := lab lam k crs x z
      (ldist (C.encode crs (bits x ++ bits z))
          (bits (fun j => xor (permWord (π lam k crs a) (E lam k x z) j) (s lam k crs a j))) : ℝ) ≤
        η * C.N lam (k + v lam)

open Classical in
/-- **`Q`-pairwise column robustness** (Definition 7.4, p.49) of `E(x, z) = Ax + Bz`: with
`w = ⌈√v⌉`, for every pair of permutations `π₁`, `π₂` of `[N]`, a uniform `w`-subset `S ⊆ [N]`
satisfies `Pr_S[rank(B_U) = |U|] ≥ 1/Q(k, v)` for `U = π₁^{−1}(S) ∪ π₂^{−1}(S)` (7.3), where `B_U` is the
matrix of the rows of `B` indexed by `U`.

**Formalization Note** Row `i` of `B` is `j ↦ E(0, e_j)_i` over `𝔽₂ = ZMod 2`; `rank(B_U) = |U|` is
linear independence of these rows over `U`. With the permutation convention of `permWord`,
`π^{−1}(S)` is the image of `S` under `π^{−1}`. The bound `Pr ≥ 1/Q` is written
`#{w-subsets} ≤ Q · #{good w-subsets}`, so `Q = 0` does not make it vacuous. -/
def ColRobust {k v N : ℕ} (E : (Fin k → Bool) → (Fin v → Bool) → Fin N → Bool) (Q : ℕ) : Prop :=
  let row : Fin N → Fin v → ZMod 2 := fun i j =>
    if E (fun _ => false) (fun j' => decide (j' = j)) i then 1 else 0
  ∀ π₁ π₂ : Equiv.Perm (Fin N),
    (((Finset.univ : Finset (Fin N)).powersetCard (Nat.ceil (Real.sqrt v))).card : ℝ) ≤
      Q * ((((Finset.univ : Finset (Fin N)).powersetCard (Nat.ceil (Real.sqrt v))).filter (fun S : Finset (Fin N) =>
        LinearIndependent (ZMod 2)
          (fun i : ↥(S.image π₁.symm ∪ S.image π₂.symm) => row i.val))).card : ℝ)

end SeededShannon.Supplement


