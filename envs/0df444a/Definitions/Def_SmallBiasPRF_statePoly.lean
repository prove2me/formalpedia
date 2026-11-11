-- Prove2me | Definitions.Def_SmallBiasPRF_statePoly
-- name    : SmallBiasPRF_statePoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:13.415416+00:00
-- url     : https://prove2.me/theorems/2e711662-3051-4b7d-ab6d-0f5c2b9d981f
-- title:
--   The polynomial framework: $V_B$, multilinear polynomials, $\delta_{B,v}$, $Q_{B,S}$, $\mathrm{gap}_B$, $\Psi_B$, $N_B(S)$
-- statement:
--   Fix a nonempty finite set $B\subseteq\mathbb F_2^n$, let $V_B=\operatorname{span}_{\mathbb F_2}(B)$, $D_B=\dim V_B$, and choose a basis $X_{B,1},\dots,X_{B,D_B}$ of the dual space $V_B^*$. Work in the ring of multilinear polynomials
--
--   $$R_B=\mathbb F_4[X_{B,1},\dots,X_{B,D_B}]/(X_{B,i}^2-X_{B,i}),\qquad \mathbb F_4=\mathbb F_2(\omega),\ \omega^2+\omega+1=0.$$
--
--   1. The **point indicator** of $v\in V_B$ is $\delta_{B,v}=\prod_{i:X_{B,i}(v)=1}X_{B,i}\prod_{i:X_{B,i}(v)=0}(1+X_{B,i})$.
--   2. The **point-function polynomial** of a state $S:B\to\mathbb F_3$ is $Q_{B,S}=\sum_{a\in B}\omega^{S(a)}\delta_{B,a}$, display (17).
--   3. The **gap** is $\mathrm{gap}_B(S)=D_B-\deg(Q_{B,S})$ and the **potential** is $\Psi_B(S)=(4/3)^{\mathrm{gap}_B(S)}$.
--   4. A functional $L=\sum_i c_iX_{B,i}\in V_B^*$ is read as a linear polynomial; with $d=\deg Q_{B,S}$, the map $\Phi_{B,S}:L\mapsto[LQ_{B,S}]^{[d+1]}$ takes the homogeneous degree-$(d+1)$ part, and $N_B(S)=\ker\Phi_{B,S}$, display (26).
--   5. A **linear update** $U:B\to\mathbb F_2$ is the restriction of a functional in $V_B^*$; the state update is $(S+\rho U)(a)=S(a)+\rho U(a)$ in $\mathbb F_3$. The code coordinate $x$ gives the functional $P_{\tilde U_x|_B}:v\mapsto H(v)_x$.
--
--   The gap measures how far a state is from contracting (Lemma 18), and the subspace $N_B(S)$ separates the updates that lower the gap from those that may raise it (Lemmas 24, 25, 28).
--
--   **Formalization Note** The basis is an arbitrary basis of $V_B^*$ indexed by a finite type. $\mathbb F_4$ is replaced by any field $K$ with an element $\omega$; the theorems assume characteristic $2$ and $\omega^2+\omega+1=0$. Multilinear polynomials are coefficient maps on monomials $X_I$, $I\subseteq$ the index set, with product $X_JX_L=X_{J\cup L}$; the degree of the zero polynomial is $0$. Expanding the product, $\delta_{B,v}=\sum_{I\supseteq O(v)}X_I$ with $O(v)=\{i:X_{B,i}(v)=1\}$. A linear update is given by its unique extension $L\in V_B^*$ (values off $V_B$ are never read). $N_B(S)$ is an $\mathbb F_2$-subspace (closure is proved in the module). States are total functions $\mathbb F_2^n\to$ `ZMod 3` read on $B$.
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.6, displays (16)–(19), pp.25–26 (PDF 28–29); §5.7, (24)–(26), pp.28–29 (PDF 31–32); §5.8–5.9, (27)–(28), p.32 (PDF 35)

import Mathlib
import Definitions.Def_SmallBiasPRF_basicF

namespace SmallBiasPRF

variable {n : ℕ}

/-- `V_B = span_{𝔽₂}(B) ⊆ 𝔽₂ⁿ` (§5.6, p.25 (PDF p.28)); `D_B = dim V_B`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.6, p.25. -/
def VB (B : Finset (Fin n → ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2))

/-- A point `a ∈ B` as an element of `V_B`. -/
def toVB (B : Finset (Fin n → ZMod 2)) {a : Fin n → ZMod 2} (ha : a ∈ B) : VB B :=
  ⟨a, Submodule.subset_span ha⟩

/-- Multilinear polynomials over a field `K` in the variables `ι`, i.e. the quotient ring
`K[X_i : i ∈ ι]/(X_i² − X_i)` of §5.6, p.25 (PDF p.28), represented by coefficient maps:
`P I` is the coefficient of the monomial `X_I = ∏_{i∈I} X_i`.

**Formalization Note.** Addition and scalar multiplication are coefficientwise; multiplication is
`MLPoly.mul` (reduced by `X_i² = X_i`). -/
abbrev MLPoly (ι K : Type*) : Type _ := Finset ι → K

namespace MLPoly

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
set_option linter.unusedSectionVars false

/-- Product in `K[X_i]/(X_i² − X_i)`: `X_J · X_L = X_{J∪L}`, so
`(P·Q)_I = ∑_{J ∪ L = I} P_J Q_L`. -/
def mul (P Q : MLPoly ι K) : MLPoly ι K :=
  fun I => ∑ J ∈ I.powerset, ∑ L ∈ I.powerset, if J ∪ L = I then P J * Q L else 0

/-- Degree of a multilinear polynomial: the largest `|I|` with a nonzero coefficient; the zero
polynomial has degree `0` (the paper's convention, Lemma 23, p.28). -/
noncomputable def deg (P : MLPoly ι K) : ℕ := by
  classical
  exact (Finset.univ.filter fun I : Finset ι => P I ≠ 0).sup Finset.card

/-- The homogeneous degree-`q` part `P^{[q]}` (§5.7, p.29 (PDF p.32)). -/
def homPart (P : MLPoly ι K) (q : ℕ) : MLPoly ι K :=
  fun I => if I.card = q then P I else 0

theorem mul_add_left (P P' Q : MLPoly ι K) : mul (P + P') Q = mul P Q + mul P' Q := by
  funext I
  simp only [mul, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun L _ => ?_
  split_ifs <;> ring

theorem mul_smul_left (c : K) (P Q : MLPoly ι K) : mul (c • P) Q = c • mul P Q := by
  funext I
  simp only [mul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun L _ => ?_
  split_ifs <;> ring

theorem homPart_add (P P' : MLPoly ι K) (q : ℕ) :
    homPart (P + P') q = homPart P q + homPart P' q := by
  funext I
  simp only [homPart, Pi.add_apply]
  split_ifs <;> simp

theorem homPart_smul (c : K) (P : MLPoly ι K) (q : ℕ) : homPart (c • P) q = c • homPart P q := by
  funext I
  simp only [homPart, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

end MLPoly

variable {B : Finset (Fin n → ZMod 2)} {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The set `{i : X_{B,i}(v) = 1}` of basis functionals equal to `1` at `v ∈ V_B`. -/
noncomputable def onesOf (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B))) (v : VB B) : Finset ι :=
  Finset.univ.filter fun i => X i v = 1

/-- The **point-indicator polynomial** of §5.6, p.26 (PDF p.29),
`δ_{B,v}(X) = ∏_{i : X_{B,i}(v)=1} X_{B,i} ∏_{i : X_{B,i}(v)=0} (1 + X_{B,i})`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.6, p.26.

**Formalization Note.** Expanding the product, `δ_{B,v} = ∑_{I ⊇ O(v)} X_I` with
`O(v) = {i : X_{B,i}(v) = 1}` (each factor `1 + X_i` contributes `1` or `X_i`); the coefficient map
records exactly that. -/
noncomputable def delta (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B))) (v : VB B) : MLPoly ι K :=
  fun I => if onesOf X v ⊆ I then 1 else 0

/-- The **point-function polynomial** `Q_{B,S}(X) = ∑_{a∈B} ω^{S(a)} δ_{B,a}(X)` of a state
`S : B → 𝔽₃`, display (17), p.26 (PDF p.29), with `S(a) ∈ {0, 1, 2}` as exponent.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (17), p.26.

**Formalization Note.** The basis `X_{B,1}, …, X_{B,D_B}` of `V_B*` is an arbitrary basis `X`
indexed by a finite type `ι` (the paper's "choose a basis"; every statement is made for every
basis). `F₄ = 𝔽₂(ω)` is replaced by any field `K` with an element `ω`; the theorems assume
`CharP K 2` and `ω² + ω + 1 = 0`. The state is a total function `S : 𝔽₂ⁿ → ZMod 3` read on `B`. -/
noncomputable def statePoly (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B))) (ω : K)
    (S : (Fin n → ZMod 2) → ZMod 3) : MLPoly ι K :=
  ∑ a ∈ B.attach, ω ^ (S a.1).val • delta X (toVB B a.2)

/-- The **gap** `gap_B(S) = D_B − deg(Q_{B,S})`, display (19), p.26 (PDF p.29), with
`D_B = dim V_B`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (19), p.26.

**Formalization Note.** Natural-number subtraction; `deg(Q_{B,S}) ≤ D_B` always (there are `D_B`
variables), so no truncation occurs. -/
noncomputable def gap (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B))) (ω : K)
    (S : (Fin n → ZMod 2) → ZMod 3) : ℕ :=
  Module.finrank (ZMod 2) (VB B) - (statePoly X ω S).deg

/-- The **potential** `Ψ_B(S) = (4/3)^{gap_B(S)}`, display (28), p.32 (PDF p.35).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (28), p.32. -/
noncomputable def Psi (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B))) (ω : K)
    (S : (Fin n → ZMod 2) → ZMod 3) : ℝ :=
  (4 / 3 : ℝ) ^ gap X ω S

/-- The linear polynomial `P_L = ∑_i c_i X_{B,i}` of a functional `L = ∑_i c_i X_{B,i} ∈ V_B*`
(§5.7, p.28 (PDF p.31)), with `c_i ∈ 𝔽₂ ⊆ K`. -/
noncomputable def linPoly [CharP K 2] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    (L : Module.Dual (ZMod 2) (VB B)) : MLPoly ι K :=
  fun I => ∑ i, if I = {i} then ZMod.castHom (dvd_refl 2) K (X.repr L i) else 0

theorem linPoly_add [CharP K 2] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    (L L' : Module.Dual (ZMod 2) (VB B)) :
    (linPoly X (L + L') : MLPoly ι K) = linPoly X L + linPoly X L' := by
  funext I
  simp only [linPoly, Pi.add_apply, map_add, Finsupp.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem linPoly_smul [CharP K 2] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    (c : ZMod 2) (L : Module.Dual (ZMod 2) (VB B)) :
    (linPoly X (c • L) : MLPoly ι K) = ZMod.castHom (dvd_refl 2) K c • linPoly X L := by
  funext I
  simp only [linPoly, Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- The map `Φ_{B,S} : V_B* → R_B^{[d+1]}`, `L ↦ [L Q_{B,S}]^{[d+1]}` with `d = deg(Q_{B,S})`
(§5.7, p.29 (PDF p.32)).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.7, p.29. -/
noncomputable def Phi [CharP K 2] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B))) (ω : K)
    (S : (Fin n → ZMod 2) → ZMod 3) (L : Module.Dual (ZMod 2) (VB B)) : MLPoly ι K :=
  (MLPoly.mul (linPoly X L) (statePoly X ω S)).homPart ((statePoly X ω S).deg + 1)

/-- The subspace `N_B(S) = {L ∈ V_B* : [L Q_{B,S}]^{[d+1]} = 0} = ker Φ_{B,S}`, display (26), p.29
(PDF p.32).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (26), p.29. -/
noncomputable def Nspace [CharP K 2] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    (ω : K) (S : (Fin n → ZMod 2) → ZMod 3) : Submodule (ZMod 2) (Module.Dual (ZMod 2) (VB B)) where
  carrier := {L | Phi X ω S L = 0}
  add_mem' := by
    intro L L' hL hL'
    simp only [Set.mem_ofPred_eq, Phi] at *
    rw [linPoly_add, MLPoly.mul_add_left, MLPoly.homPart_add, hL, hL', add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Phi]
    have h0 : (linPoly X (0 : Module.Dual (ZMod 2) (VB B)) : MLPoly ι K) =
        (0 : K) • linPoly X (0 : Module.Dual (ZMod 2) (VB B)) := by
      rw [← map_zero (ZMod.castHom (dvd_refl 2) K), ← linPoly_smul, zero_smul]
    rw [h0, MLPoly.mul_smul_left, MLPoly.homPart_smul, zero_smul]
  smul_mem' := by
    intro c L hL
    simp only [Set.mem_ofPred_eq, Phi] at *
    rw [linPoly_smul, MLPoly.mul_smul_left, MLPoly.homPart_smul, hL, smul_zero]

/-- The update `U : B → 𝔽₂` given by a functional `L ∈ V_B*` (a **linear update**, §5.7, p.28
(PDF p.31)): `U(a) = L(a)` for `a ∈ V_B`.

**Formalization Note.** A linear update is parameterized by its extension `L ∈ V_B*`, which is
unique because `B` spans `V_B`; then `P_U = linPoly X L`. Values off `V_B` are set to `0` and are
never read. -/
noncomputable def updOfDual (L : Module.Dual (ZMod 2) (VB B)) : (Fin n → ZMod 2) → ZMod 2 := by
  classical
  exact fun a => if h : a ∈ VB B then L ⟨a, h⟩ else 0

/-- The state update `S ↦ S + ρU`, `(S + ρU)(a) = S(a) + ρU(a)` in `𝔽₃` (§5.7, p.27 (PDF p.30)),
with the bit `U(a)` lifted by value. -/
def addUpd (S : (Fin n → ZMod 2) → ZMod 3) (ρ : ZMod 3) (U : (Fin n → ZMod 2) → ZMod 2) :
    (Fin n → ZMod 2) → ZMod 3 :=
  fun a => S a + ρ * lift3 (U a)

/-- The functional `P_{Ũ_x|_B} ∈ V_B*`, `v ↦ H(v)_x` (p.32 (PDF p.35)): the linear extension of the
restricted update `Ũ_x|_B` generated by code coordinate `x`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.8, p.32. -/
def codeFunctional {m₁ : ℕ} (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (B : Finset (Fin n → ZMod 2)) (x : Fin m₁) : Module.Dual (ZMod 2) (VB B) :=
  (LinearMap.proj x ∘ₗ H) ∘ₗ (VB B).subtype

end SmallBiasPRF


