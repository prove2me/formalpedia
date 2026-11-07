-- Prove2me | Definitions.Def_ShadowBootstrap_recon
-- name    : ShadowBootstrap_recon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:24:09.879678+00:00
-- url     : https://prove2.me/theorems/340cccbb-3d98-4828-ae10-62f60b10ba56
-- title:
--   The recursive reconstruction (Definition 5.5, Eqs. (21)–(22), Algorithm 3) and its expectation
-- statement:
--   The initialization reconstructs $|\psi\rangle$ along the binary tree of prefixes (§5.3–5.5, Algorithm 3). Leaves $x \in \{0,1\}^n$ get $|\hat\psi_x\rangle = 1$. A node $x$ with normalized child estimates $|\hat\psi_{x0}\rangle, |\hat\psi_{x1}\rangle$ forms $|q_c\rangle := |c\rangle \otimes |\hat\psi_{xc}\rangle$ and the **reconstruction matrix** (Definition 5.5)
--   $$(B_x)_{ab} := p_x\langle q_a|\psi_x\rangle\langle\psi_x|q_b\rangle = \langle q_a|\varphi_x\rangle\langle\varphi_x|q_b\rangle,$$
--   estimates it entrywise by $(\hat B_x)_{ab} := \hat o\big(|q_b\rangle\langle q_a|\big)$ from the level-$\ell$ data (Eq. (21)), takes a normalized eigenvector $\hat\alpha$ of $\hat B_x$ for its largest eigenvalue, and sets
--   $$|\hat\psi_x\rangle := \hat\alpha_0|q_0\rangle + \hat\alpha_1|q_1\rangle. \tag{22}$$
--   The output is $|\sigma_0\rangle := |\hat\psi_\emptyset\rangle$.
--
--   The module also defines the expectation of a function of $|\hat\psi_\emptyset\rangle$ over the initialization data: independent levels, each with $N_\ell$ bases drawn from its ensemble and $S_\ell$ shots per basis.
--
--   **Formalization Note** An eigenvector rule is any function returning, on every Hermitian $2\times2$ matrix, a unit vector maximizing $v^\dagger\hat B v$ (equivalently a normalized vector of the top eigenspace, "any normalized vector in its eigenspace" when the eigenvalue is repeated). Levels are indexed by the suffix size $n - \ell$.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), §5.3–5.5, Definition 5.5, Eqs. (21)–(22), pp.17–20; Algorithm 3, p.27

import Mathlib
import Definitions.Def_ShadowBootstrap_condEst

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- `|q_c⟩ := |c⟩ ⊗ |ψ̂_{xc}⟩` (§5.3, p.18) for the child estimates `u 0, u 1 ∈ ℂ^{2^D}`: the vector
on `{0,1}^{D+1}` whose first qubit is `c` and whose remaining qubits carry `u c`. -/
def qVec {D : ℕ} (u : Fin 2 → Bits D → ℂ) (c : Fin 2) : Bits (D + 1) → ℂ :=
  fun z => if z 0 = c then u c (Fin.tail z) else 0

/-- Definition 5.5, p.18: the reconstruction matrix `(B_x)_{ab} := p_x ⟨q_a|ψ_x⟩⟨ψ_x|q_b⟩`,
written with `φ_x = √p_x |ψ_x⟩` as `⟨q_a|φ_x⟩⟨φ_x|q_b⟩`. -/
def Bmat {D : ℕ} (φ : Bits (D + 1) → ℂ) (u : Fin 2 → Bits D → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => braket (qVec u a) φ * braket φ (qVec u b)

/-- Eq. (22), p.20: `|q_α⟩ := α₀|q₀⟩ + α₁|q₁⟩`. -/
def combine {D : ℕ} (u : Fin 2 → Bits D → ℂ) (α : Fin 2 → ℂ) : Bits (D + 1) → ℂ :=
  fun z => α 0 * qVec u 0 z + α 1 * qVec u 1 z

/-- `α` is a normalized eigenvector of the Hermitian `2 × 2` matrix `B` for its largest
eigenvalue (any normalized vector of that eigenspace when it is repeated, p.20), stated as: `α` is
a unit vector maximizing the Rayleigh quotient `v†Bv` over unit vectors `v`. -/
def IsTopEigvec (B : Matrix (Fin 2) (Fin 2) ℂ) (α : Fin 2 → ℂ) : Prop :=
  vnormSq α = 1 ∧ ∀ v : Fin 2 → ℂ, vnormSq v = 1 → (braket v (B.mulVec v)).re ≤ (braket α (B.mulVec α)).re

/-- A deterministic eigenvector rule (Algorithm 3, line 9, p.27: "Choose any normalized
eigenvector α̂ corresponding to the largest eigenvalue of B̂_x"): on every Hermitian `2 × 2` matrix
it returns such an eigenvector. -/
def IsTopEigRule (choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ) : Prop :=
  ∀ B : Matrix (Fin 2) (Fin 2) ℂ, B.IsHermitian → IsTopEigvec B (choose B)

/-- The child prefix `xc ∈ {0,1}^{ℓ+1}` of `x ∈ {0,1}^ℓ` (`ℓ = n − (D+1)`), the bit `c` appended
at position `ℓ`. -/
def childPrefix {n D : ℕ} (x : Bits (n - (D + 1))) (c : Fin 2) : Bits (n - D) :=
  fun i => if h : i.1 < n - (D + 1) then x ⟨i.1, h⟩ else c

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
§5.3–5.5, pp.17–20, and Algorithm 3, p.27: the recursive reconstruction. `recon … j x` is the
estimate `|ψ̂_x⟩ ∈ ℂ^{2^j}` of the node `x ∈ {0,1}^{n−j}` (level `ℓ = n − j`): leaves (`j = 0`) get
`1 ∈ ℂ`; a node at level `ℓ` builds `|q_0⟩, |q_1⟩` from its children, estimates
`(B̂_x)_{ab} = ô(|q_b⟩⟨q_a|)` by Eqs. (20)–(21) from the level-`ℓ` data, takes `α̂ = choose B̂_x`,
and returns `|q_α̂⟩` (Eq. (22)).

**Formalization Note** Levels are indexed by the suffix size `j = n − ℓ`: `E j` is the ensemble of
the level with `j` suffix qubits, and `rec ⟨D, _⟩` holds the `N_ℓ` labelled histograms of level
`ℓ = n − (D+1)`, each over the outcomes `(x, b) ∈ {0,1}^ℓ × {0,1}^{D+1}`. `N` and `S` are indexed by
`ℓ`. Entry `(a, b)` of `B̂_x` uses the observable `|q_b⟩⟨q_a|`, matching Eq. (21)'s
`O₁ = |q₁⟩⟨q₀|` in entry `(0, 1)` and Algorithm 3, line 8. The branch `D ≥ n` never occurs in the
reconstruction of the root. -/
noncomputable def recon {n : ℕ} {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    (E : (j : ℕ) → Primitive j (ι j)) (choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ)
    (N S : ℕ → ℕ)
    (rec : (j : Fin n) → Fin (N (n - (j.1 + 1))) →
      ι (j.1 + 1) × (Bits (n - (j.1 + 1)) × Bits (j.1 + 1) → ℕ)) :
    (j : ℕ) → Bits (n - j) → Bits j → ℂ
  | 0 => fun _ _ => 1
  | D + 1 => fun x =>
      let u : Fin 2 → Bits D → ℂ := fun c => recon E choose N S rec D (childPrefix x c)
      let Bh : Matrix (Fin 2) (Fin 2) ℂ :=
        if h : D < n then
          fun a b => condEst (E (D + 1)) x (ketbra (qVec u b) (qVec u a)) (S (n - (D + 1)))
            (rec ⟨D, h⟩)
        else 0
      combine u (choose Bh)

/-- The output `|σ₀⟩ := |ψ̂_∅⟩` of the reconstruction (Algorithm 3, line 13). -/
noncomputable def initOutput {n : ℕ} {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    (E : (j : ℕ) → Primitive j (ι j)) (choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ)
    (N S : ℕ → ℕ)
    (rec : (j : Fin n) → Fin (N (n - (j.1 + 1))) →
      ι (j.1 + 1) × (Bits (n - (j.1 + 1)) × Bits (j.1 + 1) → ℕ)) : Bits n → ℂ :=
  recon E choose N S rec n (fun _ => 0)

/-- The expectation `E[f(|ψ̂_∅⟩)]` over the initialization data (§5.2, p.17): at each level
`ℓ = 0, …, n−1` independently, `N_ℓ` bases drawn from the level's ensemble, each measured with
`I_{2^ℓ} ⊗ U` on `S_ℓ` fresh copies of `|ψ⟩`; the reconstruction reads the histograms. -/
noncomputable def initExpect {n : ℕ} {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    (E : (j : ℕ) → Primitive j (ι j)) (choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ)
    (N S : ℕ → ℕ) (ψ : Bits n → ℂ) (f : (Bits n → ℂ) → ℝ) : ℝ :=
  ∑ raw : (j : Fin n) → Fin (N (n - (j.1 + 1))) →
      ι (j.1 + 1) × (Fin (S (n - (j.1 + 1))) → Bits (n - (j.1 + 1)) × Bits (j.1 + 1)),
    (∏ j, levelWeight (E (j.1 + 1)) ψ (raw j)) *
      f (initOutput E choose N S fun j i => ((raw j i).1, histOf (raw j i).2))

end ShadowBootstrap


