-- Prove2me | Definitions.Def_ErschlerZheng_Germs
-- name    : ErschlerZheng_Germs
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-05T21:07:34.477199+00:00
-- url     : https://prove2.me/theorems/29f78b41-b544-4d47-a82a-0589e719bc4e
-- title:
--   Erschler–Zheng §3 — germs, isotropy groups, the auxiliary group, the sub-groupoid ℋ(H_o) and germ configurations
-- statement:
--   Definitions from §3 of Erschler and Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (pp. 17–19 of arXiv:1802.09077v2), with the orbits `rightOrbit` of the Walks bundle. An ambient group $H$ acts on a topological space $X$ from the right, `x <• h`, and by homeomorphisms (`ContinuousConstSMul Hᵐᵒᵖ X`: each map $x \mapsto x \cdot h$ is continuous); the paper's groups $G$ and $L$ are subgroups of $H$, and $\langle G, L \rangle$ is `G ⊔ L`. This is p. 17: “Let $G$ be a group acting by homeomorphisms on $\mathcal X$ from the right.” Continuity is a binder of the definitions that need the group of germs, as in the quoted sentence; `GermGroup x` uses it for the normality of `trivialNear x` in the stabilizer.
--
--   - `pointStab K x` is the stabilizer $\mathrm{St}_K(x) = \{k \in K : x \cdot k = x\}$, as on p. 13: “$\mathrm{St}_G(u) = \{g \in G : u \cdot g = u\}$”.
--   - `GermEq x h₁ h₂` says that $h_1$ and $h_2$ agree on a neighbourhood of $x$, the equality of germs of p. 17: “A *germ* of homeomorphism of $\mathcal X$ is an equivalence class of pairs $(g, x)$ where $x \in \mathcal X$ and $g$ is a homeomorphism between a neighborhood of $x$ and a neighborhood of $g(x)$; and two germs $(g_1, x_1)$ and $(g_2, x_2)$ are equal if $x_1 = x_2$ and $g_1, g_2$ coincide on a neighborhood of $x_1$.” The bundle takes germs of elements of a group acting on all of $\mathcal X$, not of homeomorphisms between neighbourhoods, which is the case the paper uses; neither element need fix $x$.
--   - `trivialNear x`, `GermGroup x` and `germ x h` are p. 17: “For $x \in \mathcal X$, the isotropy group of $\mathcal G$ at $x$, denoted by $\mathcal G_x$, is the set of germs $\{(g, x) : g \in \mathrm{St}_G(x)\}$. In other words, $\mathcal G_x$ is the quotient of the stabilizer $\mathrm{St}_G(x)$ by the subgroup of $G$ which consists of elements acting trivially on a neighborhood of $x$.” `GermGroup x` is this quotient for the whole ambient group: $\mathrm{St}_H(x)$ modulo `trivialNear x`, the elements of $\mathrm{St}_H(x)$ that fix every point of a neighbourhood of $x$. Germs at different points belong to different groups. `germ x h` is the germ $(h, x)$ of an element fixing $x$, and is the identity germ for an element that moves $x$ (a junk value). A germ $(g, x)$ of an element that moves $x$, an arrow of the paper's groupoid rather than an element of an isotropy group, is represented by the pair $(g, x) \in H \times X$.
--   - `isotropy K x` is the subgroup of `GermGroup x` formed by the germs of the elements of $K$ fixing $x$: $\mathcal G_x$ for $K = G$, and $\hat{\mathcal G}_x$ for $K = $ `G ⊔ L`, after p. 17: “With the auxiliary group $L$ chosen, let $\hat{\mathcal G}$ be the groupoid of germs of the group $\langle G, L \rangle$. The isotropy group $\hat{\mathcal G}_x$ is called the group of germs in [25].” Both are subgroups of the same group, so the hypothesis $\hat{\mathcal G}_o = \mathcal G_o$ of Proposition 3.3 is an equality of subgroups.
--   - `IsAuxiliary G L` is p. 17: “Suppose there is a group $L$ acting by homeomorphisms on $\mathcal X$ such that for any point $x \in \mathcal X$, the orbits $x \cdot L = x \cdot G$ and the isotropy group $\mathcal L_x$ of its groupoid $\mathcal L$ is trivial. We refer to such an $L$ as an *auxiliary group with trivial isotropy*.” It says $x \cdot L = x \cdot G$ and `isotropy L x = ⊥` for every point $x$.
--   - `transport L x y` is a chosen $\sigma \in L$ with $x \cdot \sigma = y$ (a Hilbert choice), and an unspecified element of $H$ when there is none; `transport L x x` need not be $1$. It supplies the choices of Notation 3.1 (p. 17), “Let $G \curvearrowright \mathcal X$ by homeomorphisms and $L$ be an auxiliary group with trivial isotropy. Suppose the isotropy group $\hat{\mathcal G}_o$ of $\hat{\mathcal G}$ is non-trivial at some point $o \in \mathcal X$. Let $H_o \lneqq \hat{\mathcal G}_o$ be a proper subgroup of $\hat{\mathcal G}_o$. For each point $x \in o \cdot G$, fix a choice of $\sigma_x \in L$ such that $o \cdot \sigma_x = x$.”, as $\sigma_x = $ `transport L o x` (the paper does not ask $\sigma_o = 1$ either). The definitions `transport`, `localGermSet` and `germSubgroupoid` accept any $L$ and any subgroup $H_o$; the statements that use them (Notation 3.1's claims, Proposition 3.3) assume that $L$ is auxiliary with trivial isotropy, that $\hat{\mathcal G}_o$ is non-trivial and that $H_o$ is a proper subgroup, as Notation 3.1 does. `transport` also supplies the $\sigma$ of (3.1) and (3.3), as `transport L x (x <• g)`. That nothing depends on the choices of Notation 3.1 and (3.1) is part of the milestone `ErschlerZheng.isSubgroup_localGermSet_and_germSubgroupoid_closed`. For (3.3), when $L$ has trivial isotropy at $x$, `germConfig L g x` is the germ at $x$ of $g\sigma^{-1}$ for every $\sigma \in L$ with $x \cdot \sigma = x \cdot g$ (`ErschlerZheng.germConfig_eq_germ_mul_inv_of_isotropy_eq_bot`), so it does not depend on the choice either.
--   - `localGermSet G L o Ho x` is $H_x$ of Notation 3.1 (pp. 17–18): “Let $H_x := \{(g, x) \in \hat{\mathcal G}_x : (\sigma_x g \sigma_x^{-1}, o) \in H_0\}$, then $H_x$ is a proper subgroup of $\hat{\mathcal G}_x$.” ($H_0$ is $H_o$.) It is the set of germs at $x$ of the elements $h$ of `G ⊔ L` fixing $x$ with $(\sigma_x h \sigma_x^{-1}, o) \in H_o$. It is defined as a set; that it is a proper subgroup of $\hat{\mathcal G}_x$ is part of the same milestone.
--   - `germSubgroupoid G L o Ho` is $\mathcal H(H_o)$ of (3.1), p. 18: “Let $\mathcal H = \mathcal H(H_o)$ be the following sub-groupoid of $\mathcal G$: $\mathcal H := \{(g, x) : g \in G,\ x \in o \cdot G,\ (g\sigma^{-1}, x) \in H_x \text{ where } \sigma \in L,\ x \cdot g = x \cdot \sigma\}$.” It is a set of pairs $(g, x) \in H \times X$, with $\sigma = $ `transport L x (x <• g)`. That it is a union of germ classes, contains the identities and is closed under inverse and composition is part of the same milestone.
--   - `germConfig L g x` is the germ configuration $\Phi_g(x)$ of Fact 3.5 and (3.3), p. 19: “Let $\vartheta : G \to \mathcal W$ by defined as $\vartheta(g) = (\Phi_g, g)$ such that for $x \in o \cdot G$, $\Phi_g(x) = (g\sigma^{-1}, x) \in \mathcal G_x$, where $\sigma \in L$, $x \cdot g = x \cdot \sigma$.” It is `germ x (g * σ⁻¹)` with $\sigma = $ `transport L x (x <• g)`, an element of `GermGroup x`, defined at every point.
--   - `germAction L g Φ x` is p. 19: “The action of $G$ on $\prod_{x \in o \cdot G} \hat{\mathcal G}_x$ is given by $(\tau_g \Phi)(x) = \sigma\Phi(x \cdot g)\sigma^{-1}$, where $\sigma \in L$ satisfies $x \cdot \sigma = x \cdot g$.” Here $\Phi$ is any family $x \mapsto \Phi(x) \in$ `GermGroup x` over all of $X$; the value is the germ at $x$ of $\sigma h \sigma^{-1}$ for a chosen representative $h$ of $\Phi(x \cdot g)$ and $\sigma = $ `transport L x (x <• g)`. That it depends on neither choice and is a left action is the milestone `ErschlerZheng.germAction_wellDefined_and_mul`. The semidirect product $\mathcal W$ of p. 19 is not defined as a group; Fact 3.5 is stated through $\Phi_g$ and $\tau$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), pp. 17–19, §3 (germs, Notation 3.1)

import Definitions.Def_ErschlerZheng_Walks

/-!
# Germs, the auxiliary group, and germ configurations (Erschler–Zheng §3, pp. 17–19)

A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, arXiv:1802.09077v2; page
numbers are those of the arXiv version.

Conventions used in this file:
- An ambient group `H` acts on a topological space `X` from the right: with
  `open scoped RightActions`, `x <• h` is `MulOpposite.op h • x` for `MulAction Hᵐᵒᵖ X`, so that
  `x <• (h₁ * h₂) = (x <• h₁) <• h₂`. The acting groups `G` and `L` are subgroups of `H`.
- The group structure on germs, and every definition that uses it, assumes that `H` acts by
  homeomorphisms: `ContinuousConstSMul Hᵐᵒᵖ X`.
- A germ `(h, x)` of an element `h` fixing `x` is an element of `GermGroup x`; germ groups at
  different points are different types.
- `germ x h` is `1` when `h` does not fix `x`; `transport L x y` is an unspecified element of `H`
  when no element of `L` maps `x` to `y`.
-/

namespace ErschlerZheng

open scoped RightActions

section Stabilizer

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X]

/-- pp. 13, 17: the stabilizer `St_K(x) = {h ∈ K : x·h = x}`. -/
def pointStab (K : Subgroup H) (x : X) : Subgroup H :=
  K ⊓
    { carrier := {h | x <• h = x}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [← op_smul_op_smul, ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        calc x <• a⁻¹ = (x <• a) <• a⁻¹ := by rw [ha]
          _ = x := by rw [op_smul_op_smul, mul_inv_cancel, MulOpposite.op_one, one_smul] }

end Stabilizer

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]

/-- p. 17: `h₁` and `h₂` agree on a neighbourhood of `x`. -/
def GermEq (x : X) (h₁ h₂ : H) : Prop := ∀ᶠ y in nhds x, y <• h₁ = y <• h₂

/-- p. 17: the elements fixing `x` that act trivially on a neighbourhood of `x`. -/
def trivialNear (x : X) : Subgroup (pointStab (⊤ : Subgroup H) x) where
  carrier := {h | GermEq x (h : H) 1}
  one_mem' := Filter.Eventually.of_forall fun _ => rfl
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, GermEq, MulOpposite.op_one, one_smul] at ha hb ⊢
    filter_upwards [ha, hb] with y hay hby
    rw [Subgroup.coe_mul, ← op_smul_op_smul, hay, hby]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, GermEq, MulOpposite.op_one, one_smul] at ha ⊢
    filter_upwards [ha] with y hay
    calc y <• ((a⁻¹ : pointStab (⊤ : Subgroup H) x) : H)
        = (y <• (a : H)) <• ((a : H))⁻¹ := by rw [hay, InvMemClass.coe_inv]
      _ = y := by rw [op_smul_op_smul, mul_inv_cancel, MulOpposite.op_one, one_smul]

variable [ContinuousConstSMul Hᵐᵒᵖ X]

instance (x : X) : (trivialNear (H := H) x).Normal := by
  refine ⟨fun n hn g => ?_⟩
  simp only [trivialNear, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, GermEq, MulOpposite.op_one, one_smul] at hn ⊢
  have hgx : x <• ((g : H)) = x := (Subgroup.mem_inf.mp g.2).2
  have hcont : Filter.Tendsto (fun y : X => y <• (g : H)) (nhds x) (nhds x) := by
    have := (continuous_const_smul (MulOpposite.op (g : H))).tendsto x
    rwa [hgx] at this
  filter_upwards [hn, hcont.eventually hn] with y hy hgy
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [← op_smul_op_smul, ← op_smul_op_smul, hgy, op_smul_op_smul, mul_inv_cancel,
    MulOpposite.op_one, one_smul]

/-- p. 17: the group of germs at `x` of the elements of `H` fixing `x`. -/
abbrev GermGroup (x : X) : Type _ := pointStab (⊤ : Subgroup H) x ⧸ trivialNear x

open scoped Classical in
/-- p. 17: the germ `(h, x)` of `h` at `x` (the identity germ if `h` does not fix `x`). -/
noncomputable def germ (x : X) (h : H) : GermGroup (H := H) x :=
  if hx : x <• h = x then QuotientGroup.mk ⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hx⟩⟩
  else 1

/-- p. 17: the isotropy group at `x` of the groupoid of germs of `K`: the germs at `x` of the
elements of `K` fixing `x`. -/
def isotropy (K : Subgroup H) (x : X) : Subgroup (GermGroup (H := H) x) :=
  ((pointStab K x).subgroupOf (pointStab ⊤ x)).map (QuotientGroup.mk' _)

/-- p. 17: `L` is an auxiliary group with trivial isotropy for `G`: `x·L = x·G` for every `x`, and
every isotropy group of `L` is trivial. -/
def IsAuxiliary (G L : Subgroup H) : Prop :=
  (∀ x : X, rightOrbit L x = rightOrbit G x) ∧ ∀ x : X, isotropy L x = ⊥

/-- p. 17 ("fix a choice of `σ_x ∈ L` such that `o·σ_x = x`") and (3.1), p. 18: a chosen
`σ ∈ L` with `x·σ = y`. -/
noncomputable def transport (L : Subgroup H) (x y : X) : H :=
  Classical.epsilon fun σ => σ ∈ L ∧ x <• σ = y

/-- Notation 3.1, pp. 17–18: `H_x = {(h, x) ∈ Ĝ_x : (σ_x h σ_x⁻¹, o) ∈ H_o}`, where `Ĝ_x` consists
of the germs at `x` of the elements of `G ⊔ L` fixing `x`, and `σ_x = transport L o x`. -/
noncomputable def localGermSet (G L : Subgroup H) (o : X) (Ho : Subgroup (GermGroup (H := H) o))
    (x : X) : Set (GermGroup (H := H) x) :=
  {γ | ∃ h ∈ G ⊔ L, x <• h = x ∧ germ x h = γ ∧
    germ o (transport L o x * h * (transport L o x)⁻¹) ∈ Ho}

/-- (3.1), p. 18: `ℋ(H_o) = {(g, x) : g ∈ G, x ∈ o·G, (gσ⁻¹, x) ∈ H_x where σ ∈ L, x·g = x·σ}`,
as a set of pairs `(g, x)`, with `σ = transport L x (x·g)`. -/
noncomputable def germSubgroupoid (G L : Subgroup H) (o : X)
    (Ho : Subgroup (GermGroup (H := H) o)) : Set (H × X) :=
  {p | p.1 ∈ G ∧ p.2 ∈ rightOrbit G o ∧
    germ p.2 (p.1 * (transport L p.2 (p.2 <• p.1))⁻¹) ∈ localGermSet G L o Ho p.2}

/-- (3.3), p. 19: the germ configuration `Φ_g(x) = (gσ⁻¹, x)`, with `σ = transport L x (x·g)`. -/
noncomputable def germConfig (L : Subgroup H) (g : H) (x : X) : GermGroup (H := H) x :=
  germ x (g * (transport L x (x <• g))⁻¹)

/-- p. 19: `(τ_g Φ)(x) = σ Φ(x·g) σ⁻¹`, with `σ = transport L x (x·g)`, computed on the chosen
representative `(Φ (x·g)).out` of the germ `Φ(x·g)`. -/
noncomputable def germAction (L : Subgroup H) (g : H) (Φ : (x : X) → GermGroup (H := H) x)
    (x : X) : GermGroup (H := H) x :=
  germ x (transport L x (x <• g) * ((Φ (x <• g)).out : H) * (transport L x (x <• g))⁻¹)

end ErschlerZheng


