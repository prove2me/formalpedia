-- Prove2me | Definitions.Def_GL2QFT_Supplement_LittleGroup
-- name    : GL2QFT_Supplement_LittleGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:37:54.976143+00:00
-- url     : https://prove2.me/theorems/bc5f20ab-70ad-43d5-b11f-807fbec96c39
-- title:
--   Little group basis, orbit transport, the right-coset induction transform (212) and Algorithm 2
-- statement:
--   The objects of §7.2–7.3 for $N\trianglelefteq G$.
--
--   1. A **label transversal** $T_\sigma$ (Definition 7.2): one representative of each class of $g_1\sim g_2\iff(g_1)\sigma=(g_2)\sigma$, with $g_{\sigma,\sigma}=1$; the **orbit encoding** $\lambda\mapsto(\sigma,t_L)$, $\lambda=(t_L)\sigma$ (202).
--   2. **Orbit transport intertwiners** (Definition 7.4): unitaries $U_{t,\sigma}:V_\sigma\to V_{(t)\sigma}$ with $U_{t,\sigma}R^t_\sigma(n)U^\dagger_{t,\sigma}=R_{(t)\sigma}(n)$ and $U_{1,\sigma}=\mathrm{id}$.
--   3. The irreps $R_{(\sigma,\eta')}=\mathrm{Ind}^G_{I_\sigma}(R^{\rm ext}_\sigma\otimes\tilde R_{\eta'})$ in the **little group basis** $|t,i_\sigma,j_{\eta'}\rangle$ (198).
--   4. The **right-coset induction transform** (212): with the $N$-adapted basis $|k_\lambda:\lambda\xrightarrow{j}(\sigma,\eta')\rangle=|t_L\rangle\otimes U^\dagger_{t_L,\sigma}|k_\lambda\rangle\otimes|j_{\eta'}\rangle$ (199),
--   $$[U^\lambda_{\rm Ind}]^{(\sigma,\eta'),j;\,t_R,k^*_\sigma,l^*_{\eta'}}_{k^*_\lambda,h}=\sqrt{\frac{d_{(\sigma,\eta')}}{d_\lambda|T_N|}}\,\langle k_\lambda:\lambda\xrightarrow{j}(\sigma,\eta')|R_{(\sigma,\eta')}(h)|t_R,k_\sigma,l_{\eta'}\rangle .$$
--   5. **Steps 3–8 of Algorithm 2** (without $U^L_{\rm orb}$) on the right $N$-Fourier register: $U^R_{\rm orb}$, the factorization $h=t_Lat_R^{-1}$ (Definition 7.18), $(R^{\rm ext}_\sigma)^*(a^{-1})$, $a\mapsto aN$, and $\mathfrak F_{H_\sigma}$; and the whole of **Algorithm 2** (Steps 1–8) as an operator $\mathbb C[G]\to\bigoplus V_{(\sigma,\eta')}\otimes V^*_{(\sigma,\eta')}$.
--
--   **Formalization Note** The algorithm's operator is written as the product of its steps' matrices, with the classical steps (the encodings $g=nh$, $\lambda\mapsto(\sigma,t_L)$, $h\mapsto(a,t_R)$, $a\mapsto aN$) entering as the unique solutions they compute.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Definitions 7.2, 7.4, 7.14, 7.16–7.18, eqs. (198)–(207), Algorithm 2, eq. (212), pp.56–64 (PDF pp.57–65)

import Definitions.Def_GL2QFT_Supplement_RepTheory

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

namespace LittleGroup

open scoped Matrix ComplexConjugate

variable {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
  {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
  (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (O : Set ΛN) (Tσ : ΛN → Set G)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Definition 7.2, item 2, eqs. (173)–(176),
p.56 (PDF p.57): `T_σ ⊆ G` contains exactly one representative of each class of `g₁ ∼ g₂ ⟺
(g₁)σ = (g₂)σ` (i.e. `R^{g₁}_σ ≅ R^{g₂}_σ`), normalized by `g_{σ,σ} = 1_G` (176). -/
def IsLabelTransversal (σ : ΛN) : Prop :=
  (1 : G) ∈ Tσ σ ∧
    ∀ g : G, ∃! t : Tσ σ, RepEquiv (transport N (RN σ) (t : G)) (transport N (RN σ) g)

/-- arXiv:2608.28573, Definition 7.16, eq. (202), p.62 (PDF p.63): the orbit encoding sends `λ` to
`(σ, t_L)` with `σ = r_{O(N̂)}(λ) ∈ O` and `t_L = g_{σ,λ} ∈ T_σ`, `λ = (t_L)σ` (`R_λ ≅ R^{t_L}_σ`). -/
def IsOrbEnc (l σ : ΛN) (t : G) : Prop :=
  σ ∈ O ∧ t ∈ Tσ σ ∧ RepEquiv (RN l) (transport N (RN σ) t)

variable (U : ∀ σ : ΛN, G → ∀ l : ΛN, Matrix (BN l) (BN σ) ℂ)

/-- arXiv:2608.28573, Definition 7.4, eqs. (177)–(178), p.56 (PDF p.57): the orbit transport
intertwiners: for `σ ∈ O`, `t ∈ T_σ` and `λ = (t)σ`, `U_{t,σ} : V_σ → V_λ` is unitary with
`U_{t,σ} R^t_σ(n) U_{t,σ}† = R_λ(n)` for `n ∈ N`; normalized by `U_{1_G,σ} = id_{V_σ}`. -/
def IsOrbitTransport : Prop :=
  (∀ σ ∈ O, U σ 1 σ = 1) ∧
    ∀ l σ t, IsOrbEnc N BN RN O Tσ l σ t →
      U σ t l * (U σ t l)ᴴ = 1 ∧ (U σ t l)ᴴ * U σ t l = 1 ∧
        ∀ n : N, U σ t l * transport N (RN σ) t n * (U σ t l)ᴴ = RN l n

variable (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
  {Λη : ΛN → Type} [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
  [∀ σ η, DecidableEq (Bη σ η)]
  (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) → Matrix (Bη σ η) (Bη σ η) ℂ)

/-- arXiv:2608.28573, Definition 7.14, eq. (198), p.61 (PDF p.62): the little group basis
`|t, i_σ, j_{η′}⟩`, `t ∈ T_σ`, of `V_(σ,η′) = Ind^G_{I_σ}(V_σ ⊗ V_{η′})`. -/
abbrev LBas (σ : ΛN) (η : Λη σ) : Type := Tσ σ × (BN σ × Bη σ η)

/-- arXiv:2608.28573, Theorem 7.12, eq. (196), and Definition 7.14, p.60–61: the irreducible
representation `R_(σ,η′) = Ind^G_{I_σ}(R^ext_σ ⊗ R̃_{η′})` with transversal `T_σ`, in the little
group basis. -/
def littleRep (σ : ΛN) (η : Λη σ) (g : G) : Matrix (LBas BN Tσ Bη σ η) (LBas BN Tσ Bη σ η) ℂ :=
  indRep (inertia N RN σ) (Tσ σ)
    (fun k => Matrix.kronecker (Rext σ k) (inflation N RN σ (Rη σ η) k)) g

variable (TN : Set G)

/-- The output index of the right-coset induction transform for fixed `σ`: `((σ, η′), j;
t_R, k*_σ, l*_{η′})`, with `j` the multiplicity label (`j = 1, …, d_{η′}`, p.64). -/
abbrev ROut (σ : ΛN) : Type := Σ η : Λη σ, Bη σ η × LBas BN Tσ Bη σ η

/-- arXiv:2608.28573, Definition B.3 (right-coset version) and eq. (212), p.64 (PDF p.65): for
`λ = (t_L)σ`, the `λ`-induction transform on the right `N`-Fourier register,
`U^λ_Ind : V*_λ ⊗ ℂ[T_N] → ⊕_{η′} ℂ^{m_{λ,(σ,η′)}} ⊗ V*_(σ,η′)`,
`[U^λ_Ind]^{(σ,η′),j; t_R,k*_σ,l*_{η′}}_{k*_λ, h} = √(d_(σ,η′)/(d_λ |T_N|))
⟨k_λ : λ →^j (σ,η′)| R_(σ,η′)(h) |t_R, k_σ, l_{η′}⟩`, where the `N`-adapted basis vector (199) is
`|k_λ : λ →^j (σ,η′)⟩ = |t_L⟩ ⊗ U†_{t_L,σ}|k_λ⟩ ⊗ |j_{η′}⟩`, so that
`⟨k_λ : λ →^j (σ,η′)| = Σ_i [U_{t_L,σ}]^{k_λ}_{i} ⟨t_L, i, j|`. -/
def uIndRight (l σ : ΛN) (tL : Tσ σ) :
    Matrix (ROut BN Tσ Bη σ) (BN l × TN) ℂ :=
  Matrix.of fun o kh =>
    (Real.sqrt ((Fintype.card (LBas BN Tσ Bη σ o.1) : ℝ) /
      ((Fintype.card (BN l) : ℝ) * (Fintype.card TN : ℝ))) : ℂ) *
      ∑ i : BN σ, U σ tL l kh.1 i *
        littleRep N BN RN Tσ Rext Bη Rη σ o.1 (kh.2 : G) (tL, (i, o.2.1)) o.2.2

/-- arXiv:2608.28573, Algorithm 2, Steps 3–8 with `U^L_orb` omitted from Step 4, p.63 (PDF p.64),
for the irrep label `λ` encoded (Step 3) as `(σ, t_L)`, acting on the right `N`-Fourier register
`|k*_λ⟩` and the coset register `|h⟩`, `h ∈ T_N`:
* Step 4 (`U^R_orb`): `|k*_λ⟩ ↦ U^T_{t_L,σ}|k*_λ⟩`, entry `[U_{t_L,σ}]^{k_λ}_{k''}`;
* Step 5: `|h⟩ ↦ |a⟩|t_R⟩` with `h = t_L a t_R⁻¹`, `a ∈ I_σ`, `t_R ∈ T_σ` (Definition 7.18): the
  output `t_R` occurs exactly when `a = t_L⁻¹ h t_R ∈ I_σ`;
* Step 6: `(R^ext_σ)^*(a⁻¹) = R^ext_σ(a)^T` on the right Fourier register, entry
  `[R^ext_σ(a)]^{k''}_{k_σ}`;
* Step 7: `|a⟩ ↦ |aN⟩` (factor `a = h_σ d`, uncompute `d`, relabel `h_σ ≡ aN`);
* Step 8: `F_{H_σ}` on `|aN⟩`, entry `√(d_{η′}/|H_σ|) [R_{η′}(aN)]^j_l` (22). -/
def stepsRight (l σ : ΛN) (tL : Tσ σ) :
    Matrix (ROut BN Tσ Bη σ) (BN l × TN) ℂ :=
  Matrix.of fun o kh =>
    if hm : (tL : G)⁻¹ * (kh.2 : G) * (o.2.2.1 : G) ∈ inertia N RN σ then
      ∑ k'' : BN σ, U σ tL l kh.1 k'' * Rext σ ⟨_, hm⟩ k'' o.2.2.2.1 *
        ((Real.sqrt ((Fintype.card (Bη σ o.1) : ℝ) /
            (Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) : ℝ)) : ℂ) *
          Rη σ o.1 (QuotientGroup.mk ⟨_, hm⟩) o.2.1 o.2.2.2.2)
    else 0

/-- The labels `(σ, η′)`, `σ ∈ O`, `η′ ∈ Ĥ_σ`, of the irreps of `G` (195). -/
abbrev GLab : Type := Σ σ : O, Λη σ.1

/-- arXiv:2608.28573, Algorithm 2 (Steps 1–8), p.63 (PDF p.64), as an operator `ℂ[G] →
⊕_{(σ,η′)} V_(σ,η′) ⊗ V*_(σ,η′)`, with the output `|σ, η′⟩ ⊗ |t_L, i_σ, j_{η′}⟩ ⊗ |t_R, k*_σ, l*_{η′}⟩`:
* Step 1: `|g⟩ ↦ |n⟩|h⟩`, `g = nh`, `n ∈ N`, `h ∈ T_N`;
* Step 2: `F_N` (22): `√(d_λ/|N|) [R_λ(n)]^{i_λ}_{k_λ}`;
* Step 3: `λ ↦ (σ, t_L)` (202);
* Step 4: `U^L_orb`: `|i_λ⟩ ↦ U†_{t_L,σ}|i_λ⟩`, entry `conj [U_{t_L,σ}]^{i_λ}_{i_σ}`, and `U^R_orb`;
* Steps 4 (`U^R_orb`)–8: `stepsRight`.

**Formalization Note** Step 1 picks the unique `h ∈ T_N` with `g h⁻¹ ∈ N`; Step 3 is the sum over
the `λ` encoded as the output's `(σ, t_L)`. -/
def alg2 :
    Matrix (Σ p : GLab O (Λη := Λη),
        LBas BN Tσ Bη p.1.1 p.2 × LBas BN Tσ Bη p.1.1 p.2) G ℂ :=
  Matrix.of fun o g =>
    if hg : ∃ h : TN, g * (h : G)⁻¹ ∈ N then
      ∑ l : ΛN,
        if IsOrbEnc N BN RN O Tσ l o.1.1.1 (o.2.1.1 : G) then
          ∑ i' : BN l, ∑ k' : BN l,
            (Real.sqrt ((Fintype.card (BN l) : ℝ) / (Fintype.card N : ℝ)) : ℂ) *
              RN l ⟨_, Classical.choose_spec hg⟩ i' k' *
              conj (U o.1.1.1 o.2.1.1 l i' o.2.1.2.1) *
              stepsRight N BN RN Tσ U Rext Bη Rη TN l o.1.1.1 o.2.1.1
                ⟨o.1.2, o.2.1.2.2, o.2.2⟩ (k', Classical.choose hg)
        else 0
    else 0

end LittleGroup

end Supplement

end GL2QFT


