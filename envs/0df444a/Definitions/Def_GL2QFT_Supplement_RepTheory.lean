-- Prove2me | Definitions.Def_GL2QFT_Supplement_RepTheory
-- name    : GL2QFT_Supplement_RepTheory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:34:53.875+00:00
-- url     : https://prove2.me/theorems/922d4bfa-8a08-4c8e-9f8a-71704c568bc8
-- title:
--   Irrep systems, induced representations, twisted modules and the Clifford data of §7.1–7.2
-- statement:
--   General representation-theoretic vocabulary for the supplement, on top of the published `GL2QFT.RepBasics` (matrix representations in fixed orthonormal bases).
--
--   1. **Irrep system** (§2.1). A family $(R_\lambda)_{\lambda\in\Lambda}$ of matrix representations of $G$ is a choice of representatives of the unitary dual $\widehat G$ if every $R_\lambda$ is unitary and irreducible, $R_\lambda\not\cong R_\mu$ for $\lambda\neq\mu$, and every irreducible representation of $G$ is equivalent to some $R_\lambda$.
--   2. **Induced representation** (Definition 2.10, eq. (27)). For $K\le G$, a left transversal $\mathcal T$ and a representation $R$ of $K$,
--   $$[(\mathrm{Ind}^G_K R)(g)]^{s,j}_{t,i}=\delta_{s,t_g}[R(h_g)]^j_i,\qquad gt=t_gh_g .$$
--   3. **Double-coset transversal** $\Omega$ for $H\backslash G/K$, the intersection subgroup $H_\omega=H\cap\omega H\omega^{-1}$ and the **twisted module** $R^\omega(h)=R(\omega^{-1}h\omega)$ (Lemma 5.1, eq. (61)).
--   4. The tensor product $\bigotimes_r M_r$ of a finite family of matrices, and the support relation "$R_{\rm small}$ occurs in $\mathrm{Res}\,R_{\rm big}$" (Definition 2.12).
--   5. **Clifford data** for $N\trianglelefteq G$ (§7.1–7.2): the transported representation $R^g_\lambda(n)=R_\lambda(g^{-1}ng)$ (169); the orbit relation $\mu=(g)\lambda$ ($R_\mu\cong R^g_\lambda$, (170)); the **inertia group** $I_\lambda=\{g:R^g_\lambda\cong R_\lambda\}$ (Definition 7.1); a set $O(\widehat N)$ of orbit representatives (Definition 7.2); the successor relation $\eta\in N^+_{N\le I_\sigma}(\sigma)$ ((29), (184)); **extensions** $R^{\rm ext}_\lambda$ of $R_\lambda$ to $I_\lambda$ (Definition 7.9) and **inflations** $\tilde R(k)=R(kN)$ from the little group $I_\lambda/N$ (Definition 7.10).
--
--   These objects state Theorems 7.8, 7.12, 7.20, 7.21, 8.7 and the Mackey theorems 5.4 and C.2.
--
--   **Formalization Note** The inertia group is built as a subgroup from the equivalence $R^g_\lambda\cong R_\lambda$; the little group $H_\lambda=I_\lambda/N$ is the quotient of $I_\lambda$ by $N\cap I_\lambda$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §2.1 p.13, Definition 2.10 eq. (27) p.16, Definition 2.12 p.16, Lemma 5.1 eq. (61) p.28, §7.1–7.2 eqs. (169)–(190) pp.55–59 (PDF pp.14, 17, 29, 56–60)

import Definitions.Def_GL2QFT_RepBasics

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

/-- Bruinsma–Posta–Stokvis–Grinko–Ozols, *Quantum Fourier transform toolbox*, arXiv:2608.28573
(held version, sha256 ecd45073…), §2.1, p.13 (PDF p.14): the family `(R_λ)_{λ ∈ Λ}` is a choice of
representatives of the unitary dual `Ĝ` ("For each label `λ ∈ Ĝ`, we fix a `G`-module `V_λ`, a
representation `R_λ : G → U(V_λ)`, and an orthonormal basis `B_λ`"):
1. every `R_λ` is a unitary (matrix) representation;
2. every `R_λ` is irreducible;
3. `R_λ ≇ R_μ` for `λ ≠ μ`;
4. every irreducible representation of `G` is equivalent to some `R_λ`.

**Formalization Note** Matrices are taken in the fixed orthonormal basis `B λ`, as in the base
mission's `GL2QFT.RepBasics`; the index type `Λ` plays the role of the label set `Ĝ`. -/
def IsIrrepSystem {G Λ : Type} [Monoid G] {B : Λ → Type} [∀ l, Fintype (B l)]
    [∀ l, DecidableEq (B l)] (R : ∀ l, G → Matrix (B l) (B l) ℂ) : Prop :=
  (∀ l, IsUnitaryRep (R l)) ∧ (∀ l, IsIrreducibleRep (R l)) ∧
  (∀ l l', l ≠ l' → ¬ RepEquiv (R l) (R l')) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ),
    IsMatRep ρ → IsIrreducibleRep ρ → ∃ l, RepEquiv (R l) ρ)

/-- arXiv:2608.28573, Definition 2.10, eq. (27), p.16 (PDF p.17): the induced representation
`Ind^G_K R` on `ℂ[T] ⊗ V` for a left transversal `T` of `K` in `G`:
`[(Ind^G_K R)(g)]^{s,j}_{t,i} = δ_{s,t_g} [R(h_g)]^j_i`, where `g t = t_g h_g`.

**Formalization Note** The entry is written as "`s⁻¹ g t ∈ K` and then `R(s⁻¹ g t)`": when `T` is a
left transversal, `s⁻¹ g t ∈ K` holds exactly for `s = t_g`, and then `s⁻¹ g t = h_g`. -/
def indRep {G : Type} [Group G] (K : Subgroup G) (T : Set G) {ι : Type} [Fintype ι]
    (R : K → Matrix ι ι ℂ) (g : G) : Matrix (T × ι) (T × ι) ℂ :=
  Matrix.of fun sj ti =>
    if h : ((sj.1 : G)⁻¹ * g * (ti.1 : G)) ∈ K then R ⟨_, h⟩ sj.2 ti.2 else 0

/-- arXiv:2608.28573, §5, p.28 (PDF p.29): `Ω ⊆ G` contains exactly one representative of each
`(H, K)`-double coset `HgK = {hgk : h ∈ H, k ∈ K}`. -/
def IsDoubleCosetTransversal {G : Type} [Group G] (H K : Subgroup G) (Ω : Set G) : Prop :=
  ∀ g : G, ∃! ω : Ω, ∃ h ∈ H, ∃ k ∈ K, g = h * (ω : G) * k

/-- arXiv:2608.28573, Lemma 5.1 and Remark 5.2, p.28 (PDF p.29): the intersection subgroup
`H_ω = H ∩ ωHω⁻¹`, as a subgroup of `H`. -/
def interSub {G : Type} [Group G] (H : Subgroup G) (ω : G) : Subgroup H :=
  (H.map (MulAut.conj ω).toMonoidHom).subgroupOf H

theorem interSub_conj_mem {G : Type} [Group G] (H : Subgroup G) (ω : G) (h : interSub H ω) :
    ω⁻¹ * ((h : H) : G) * ω ∈ H := by
  have hm : ((h : H) : G) ∈ H.map (MulAut.conj ω).toMonoidHom := h.2
  obtain ⟨x, hx, hxh⟩ := Subgroup.mem_map.mp hm
  rw [← hxh]
  simpa [mul_assoc] using hx

/-- arXiv:2608.28573, Lemma 5.1, eq. (61), p.28 (PDF p.29): the twisted `H_ω`-module `V^ω`,
`R^ω(h)|P⟩ := R(ω⁻¹ h ω)|P⟩` for `h ∈ H_ω`. -/
def twistRep {G : Type} [Group G] (H : Subgroup G) (ω : G) {ι : Type}
    (R : H → Matrix ι ι ℂ) (h : interSub H ω) : Matrix ι ι ℂ :=
  R ⟨ω⁻¹ * ((h : H) : G) * ω, interSub_conj_mem H ω h⟩

/-- The tensor (Kronecker) product of a finite family of matrices: rows and columns are indexed by
dependent tuples, `[⊗_r M_r]^{i}_{j} = ∏_r [M_r]^{i_r}_{j_r}`. -/
def tensorFamily {I : Type} [Fintype I] {ι : I → Type} (M : ∀ r, Matrix (ι r) (ι r) ℂ) :
    Matrix (∀ r, ι r) (∀ r, ι r) ℂ :=
  Matrix.of fun i j => ∏ r, M r (i r) (j r)

/-- arXiv:2608.28573, Definition 2.12, eq. (28), p.16 (PDF p.17), for a subgroup `L ≤ K` given as
an injective homomorphism `e : L →* K`: the `L`-irrep `R_small` lies in the irreducible support of
`Res^K_L R_big`, i.e. `Hom_L(V_small, Res V_big) ≠ 0`. -/
def OccursIn {L K : Type} [Monoid L] [Monoid K] (e : L →* K) {ι κ : Type} [Fintype ι] [Fintype κ]
    (Rsmall : L → Matrix ι ι ℂ) (Rbig : K → Matrix κ κ ℂ) : Prop :=
  ∃ A : Matrix κ ι ℂ, A ≠ 0 ∧ ∀ l : L, A * Rsmall l = Rbig (e l) * A

/-! ### Clifford theory (§7.1–7.2) -/

section Clifford

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem conj_inv_mem (g : G) (n : N) : g⁻¹ * (n : G) * g ∈ N := by
  simpa using (inferInstance : N.Normal).conj_mem n n.2 g⁻¹

/-- arXiv:2608.28573, eq. (169), p.55 (PDF p.56): the transported representation
`R^g_λ(n) := R_λ(g⁻¹ n g)`, `n ∈ N`. -/
def transport {ι : Type} (R : N → Matrix ι ι ℂ) (g : G) (n : N) : Matrix ι ι ℂ :=
  R ⟨g⁻¹ * (n : G) * g, conj_inv_mem N g n⟩

variable {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
  (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ)

/-- arXiv:2608.28573, eq. (170) and Definition 7.1, pp.55–56 (PDF pp.56–57): `μ` lies in the
`G`-orbit of `λ`, i.e. `μ = (g)λ` for some `g` (`R_μ ≅ R^g_λ`). -/
def InOrbit (μ l : ΛN) : Prop := ∃ g : G, RepEquiv (RN μ) (transport N (RN l) g)

theorem transport_one {ι : Type} (R : N → Matrix ι ι ℂ) (n : N) :
    transport N R 1 n = R n := by
  unfold transport; congr 1; ext; simp

theorem transport_mul {ι : Type} (R : N → Matrix ι ι ℂ) (g₁ g₂ : G) (n : N) :
    transport N R (g₁ * g₂) n = transport N R g₂ ⟨g₁⁻¹ * (n : G) * g₁, conj_inv_mem N g₁ n⟩ := by
  unfold transport; congr 1; ext; simp [mul_assoc]

/-- arXiv:2608.28573, Definition 7.1, p.56 (PDF p.57): the inertia group
`I_λ = Stab_G(λ) = {g ∈ G : (g)λ = λ}`, i.e. the `g` with `R^g_λ ≅ R_λ`. -/
def inertia (l : ΛN) : Subgroup G where
  carrier := {g | RepEquiv (transport N (RN l) g) (RN l)}
  one_mem' := by
    refine ⟨1, 1, by simp, by simp, fun n _ => ?_⟩
    simp [transport_one]
  mul_mem' := by
    intro g₁ g₂ h₁ h₂
    obtain ⟨A₁, B₁, hAB₁, hBA₁, hA₁⟩ := h₁
    obtain ⟨A₂, B₂, hAB₂, hBA₂, hA₂⟩ := h₂
    refine ⟨A₁ * A₂, B₂ * B₁, ?_, ?_, fun n _ => ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₂, hAB₂, Matrix.one_mul, hAB₁]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc B₁, hBA₁, Matrix.one_mul, hBA₂]
    · have h1 := hA₁ n (Set.mem_univ _)
      unfold transport at h1
      rw [transport_mul, Matrix.mul_assoc, hA₂ _ (Set.mem_univ _), ← Matrix.mul_assoc, h1,
        Matrix.mul_assoc]
  inv_mem' := by
    intro g h
    obtain ⟨A, B, hAB, hBA, hA⟩ := h
    refine ⟨B, A, hBA, hAB, fun n _ => ?_⟩
    have key := hA ⟨g * (n : G) * g⁻¹, by simpa using (inferInstance : N.Normal).conj_mem n n.2 g⟩
      (Set.mem_univ _)
    have e1 : transport N (RN l) g ⟨g * (n : G) * g⁻¹, by
        simpa using (inferInstance : N.Normal).conj_mem n n.2 g⟩ = RN l n := by
      unfold transport; congr 1; ext; simp [mul_assoc]
    have e2 : transport N (RN l) g⁻¹ n = RN l ⟨g * (n : G) * g⁻¹, by
        simpa using (inferInstance : N.Normal).conj_mem n n.2 g⟩ := by
      unfold transport; congr 1; ext; simp
    rw [e1] at key
    rw [e2]
    calc B * RN l ⟨g * (n : G) * g⁻¹, _⟩
        = B * RN l ⟨g * (n : G) * g⁻¹, _⟩ * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = B * (RN l ⟨g * (n : G) * g⁻¹, _⟩ * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = B * (A * RN l n) * B := by rw [key]
      _ = RN l n * B := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]

/-- arXiv:2608.28573, Definition 7.2, item 1, eq. (172), p.56 (PDF p.57): `O ⊆ N̂` contains exactly
one representative of each `G`-orbit in `N̂`. -/
def IsOrbitTransversal (O : Set ΛN) : Prop :=
  ∀ l : ΛN, ∃! σ : O, InOrbit N RN l σ

/-- The inclusion `N → I_λ` (`N ≤ I_λ`, p.59), as a function on the elements of `N` that lie in
`I_λ` (all of them, under the standing hypotheses). -/
def inNInertia (l : ΛN) : (N.subgroupOf (inertia N RN l)) →* inertia N RN l :=
  (N.subgroupOf (inertia N RN l)).subtype

/-- The elements of `N ∩ I_λ` as elements of `N`. -/
def inertiaToN (l : ΛN) : (N.subgroupOf (inertia N RN l)) →* N where
  toFun x := ⟨((x : inertia N RN l) : G), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- arXiv:2608.28573, Definition 2.13, eq. (29), p.16, for `N ≤ I_σ` (used in (184), p.58): the
`I_σ`-irrep `R_η` is a successor of `σ`, `η ∈ N⁺_{N ≤ I_σ}(σ)`, i.e. `V_σ` occurs in
`Res^{I_σ}_N V_η`. -/
def IsSuccessor (σ : ΛN) {ι : Type} [Fintype ι] (Rη : inertia N RN σ → Matrix ι ι ℂ) : Prop :=
  ∃ A : Matrix ι (BN σ) ℂ, A ≠ 0 ∧
    ∀ x : N.subgroupOf (inertia N RN σ),
      A * RN σ (inertiaToN N RN σ x) = Rη (inNInertia N RN σ x) * A

/-- arXiv:2608.28573, Definition 7.9, eqs. (186)–(187), p.59 (PDF p.60): `R^ext : I_λ → U(V_λ)` is
a unitary representation extending `R_λ`: `Res^{I_λ}_N R^ext = R_λ`. -/
def IsExtension (l : ΛN) (Rext : inertia N RN l → Matrix (BN l) (BN l) ℂ) : Prop :=
  IsUnitaryRep Rext ∧
    ∀ x : N.subgroupOf (inertia N RN l), Rext (inNInertia N RN l x) = RN l (inertiaToN N RN l x)

/-- arXiv:2608.28573, Definition 7.10, eq. (190), p.59 (PDF p.60): the inflation
`R̃(k) := R(kN)` of a representation of the little group `H_λ = I_λ / N` to `I_λ`. -/
def inflation (l : ΛN) {ι : Type}
    (R : (inertia N RN l ⧸ N.subgroupOf (inertia N RN l)) → Matrix ι ι ℂ)
    (k : inertia N RN l) : Matrix ι ι ℂ :=
  R (QuotientGroup.mk k)

end Clifford

end Supplement

end GL2QFT


