-- Prove2me | Definitions.Def_SmallBiasPRF_basicF
-- name    : SmallBiasPRF_basicF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:40.146055+00:00
-- url     : https://prove2.me/theorems/93f5154b-3875-4226-ba02-3b7e912b1a44
-- title:
--   The construction template $F_{\pi,w,z}(a)=R(G_{w,z}(\mathrm{map}_\pi(H(a))))$ and its single-bit variant
-- statement:
--   Fix a linear code $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$ and a linear map $R:\mathbb F_2^{m_2}\to\mathbb F_2^n$. For a key $(w,z)\in\{0,1,2\}^{m_2}\times\{0,1,2\}^{m_2}$ and an input $b\in\{0,1\}^{m_2}$, define $s_0=0$,
--
--   $$s_j=(s_{j-1}+b_jw_j)\bmod 3,\qquad t_j=\big((s_j+z_j)\bmod 3\big)\bmod 2,\qquad j\in[m_2],$$
--
--   and $G_{w,z}(b)=(t_1,\dots,t_{m_2})$. A selector $\pi\in[m_1]^{m_2}$ defines $\mathrm{map}_\pi:\{0,1\}^{m_1}\to\{0,1\}^{m_2}$, $\mathrm{map}_\pi(u)_j=u_{\pi(j)}$. The **construction template** is
--
--   $$F_{\pi,w,z}(a)=R\big(G_{w,z}(\mathrm{map}_\pi(H(a)))\big),\qquad a\in\{0,1\}^n,$$
--
--   and for $S\subseteq[m_2]$ its **single-bit variant** is $F^S_{\pi,w,z}(a)=G^S_{w,z}(\mathrm{map}_\pi(H(a)))$ with $G^S_{w,z}(b)=\sum_{j\in S}t_j\bmod 2$. Finally, the **generalized construction** draws $\pi$ from an arbitrary distribution $\nu$ independently of $(w,z)$, which is uniform.
--
--   This is the alternating-moduli template of the paper: a linear encoding, a mod-3 accumulation of selected codeword bits, a mod-2 reduction and a linear compression.
--
--   **Formalization Note** Indices are 0-based. The state $s_j$ is the prefix sum $\sum_{i\le j}b_iw_i$ in `ZMod 3`, where the bit $b_i$ is lifted to $\mathbb F_3$ by value; $(s_j+z_j)\bmod 3$ is the canonical representative in $\{0,1,2\}$. The law of the generalized construction is $\nu$ bound with the uniform law on $(w,z)$.
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.1, p.13 (PDF 16); §4.1.1, p.14 (PDF 17); Lemma 10, p.17 (PDF 20)

import Mathlib

namespace SmallBiasPRF

/-- The bit `b ∈ 𝔽₂ = {0, 1}` read as an element of `𝔽₃` (`0 ↦ 0`, `1 ↦ 1`), as in §4.1 and §5.1
("the symbols 0, 1 from 𝔽₂ are identified with the corresponding elements of 𝔽₃", p.18).

**Formalization Note.** This is the lift by value; there is no ring homomorphism `𝔽₂ → 𝔽₃`. -/
def lift3 (b : ZMod 2) : ZMod 3 :=
  (b.val : ZMod 3)

/-- `r ↦ (r mod 3) mod 2`: the canonical representative of `r ∈ 𝔽₃` in `{0, 1, 2}`, reduced
modulo 2 (§4.1, p.13 (PDF p.16)). -/
def mod3mod2 (r : ZMod 3) : ZMod 2 :=
  ((r.val % 2 : ℕ) : ZMod 2)

/-- The state sequence of `G_{w,z}` (§4.1, p.13 (PDF p.16)): `s₀ = 0` and
`s_j = (s_{j−1} + b_j w_j) mod 3`, i.e. `s_j = ∑_{i ≤ j} b_i w_i` in `𝔽₃`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.1, p.13.

**Formalization Note.** Coordinates are 0-based: index `j : Fin m₂` is the paper's `j + 1`, and the
value is the prefix sum over indices `≤ j` (the recursion unrolled; `s₀ = 0` is the empty sum). -/
def prefixState {m₂ : ℕ} (w : Fin m₂ → ZMod 3) (b : Fin m₂ → ZMod 2) (j : Fin m₂) : ZMod 3 :=
  ∑ i ∈ Finset.Iic j, lift3 (b i) * w i

/-- The map `G_{w,z} : {0,1}^{m₂} → {0,1}^{m₂}` of the construction template (§4.1, p.13
(PDF p.16)): `t_j = ((s_j + z_j) mod 3) mod 2` and `G_{w,z}(b) = (t₁, …, t_{m₂})`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.1, p.13.

**Formalization Note.** Keys `w, z ∈ {0,1,2}^{m₂}` are `Fin m₂ → ZMod 3`; `(s_j + z_j) mod 3` is the
canonical representative `(s_j + z_j).val ∈ {0,1,2}`, reduced mod 2. -/
def G {m₂ : ℕ} (w z : Fin m₂ → ZMod 3) (b : Fin m₂ → ZMod 2) : Fin m₂ → ZMod 2 :=
  fun j => mod3mod2 (prefixState w b j + z j)

/-- The single-bit variant `G^S_{w,z}(b) = ∑_{j∈S} t_j mod 2` for `S ⊆ [m₂]` (§4.1.1, p.14
(PDF p.17)).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.1.1, p.14. -/
def GS {m₂ : ℕ} (S : Finset (Fin m₂)) (w z : Fin m₂ → ZMod 3) (b : Fin m₂ → ZMod 2) : ZMod 2 :=
  ∑ j ∈ S, G w z b j

/-- The coordinate selector `map_π : {0,1}^{m₁} → {0,1}^{m₂}`, `map_π(u)_j = u_{π(j)}`, for
`π ∈ [m₁]^{m₂}` (§4.1, p.13 (PDF p.16)). -/
def mapSel {m₁ m₂ : ℕ} (π : Fin m₂ → Fin m₁) (u : Fin m₁ → ZMod 2) : Fin m₂ → ZMod 2 :=
  fun j => u (π j)

/-- The **construction template** `F_{π,w,z}(a) = R(G_{w,z}(map_π(H(a))))` (§4.1, p.13 (PDF p.16)),
for a linear code `H : 𝔽₂ⁿ → 𝔽₂^{m₁}`, a linear map `R : 𝔽₂^{m₂} → 𝔽₂ⁿ`, key material
`(π, w, z) ∈ [m₁]^{m₂} × {0,1,2}^{m₂} × {0,1,2}^{m₂}` and input `a ∈ {0,1}ⁿ`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.1, p.13 (PDF p.16).

**Formalization Note.** `H` and `R` are `ZMod 2`-linear maps (the paper's standing assumption);
the code-distance and ERF properties are hypotheses of the theorems, not part of the definition.
Coordinates are 0-based. -/
def basicF {n m₁ m₂ : ℕ} (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (R : (Fin m₂ → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (π : Fin m₂ → Fin m₁)
    (w z : Fin m₂ → ZMod 3) (a : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  R (G w z (mapSel π (H a)))

/-- The single-bit variant `F^S_{π,w,z}(a) = G^S_{w,z}(map_π(H(a)))` for `S ⊆ [m₂]` (§4.1.1, p.14
(PDF p.17)). It does not involve `R`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.1.1, p.14. -/
def basicFS {n m₁ m₂ : ℕ} (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (S : Finset (Fin m₂)) (π : Fin m₂ → Fin m₁) (w z : Fin m₂ → ZMod 3) (a : Fin n → ZMod 2) :
    ZMod 2 :=
  GS S w z (mapSel π (H a))

/-- The key law of the **generalized construction** of Lemmas 10, 11 and 13 (p.17, p.19, p.21):
`π ∈ [m₁]^{m₂}` is drawn from an arbitrary distribution `ν`, independently of `(w, z)`, which is
uniform on `{0,1,2}^{m₂} × {0,1,2}^{m₂}` (§4.1, p.13).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 10, p.17
(PDF p.20).

**Formalization Note.** The product law is `ν` bound with the uniform law on `(w, z)`; its mass at
`(π, w, z)` is `ν(π)/9^{m₂}`. -/
noncomputable def selKeyLaw {m₁ m₂ : ℕ} (ν : PMF (Fin m₂ → Fin m₁)) :
    PMF ((Fin m₂ → Fin m₁) × (Fin m₂ → ZMod 3) × (Fin m₂ → ZMod 3)) :=
  ν.bind fun π =>
    (PMF.uniformOfFintype ((Fin m₂ → ZMod 3) × (Fin m₂ → ZMod 3))).map fun wz => (π, wz)

end SmallBiasPRF


