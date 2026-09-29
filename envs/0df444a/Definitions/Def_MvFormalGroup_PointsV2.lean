-- Prove2me | Definitions.Def_MvFormalGroup_PointsV2
-- name    : MvFormalGroup_PointsV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/e0356901-5752-5c00-a920-4be22ae2398c
-- title:
--   Points of a multidimensional formal group law over an ideal
-- statement:
--   Fix a commutative ring $R$, an $R$-algebra $S$ and an ideal $J \subseteq S$. The first half of the module sets up evaluation of multivariate power series in the $J$-adic topology: for an ideal $J$, a family $x : \sigma \to S$ and $f \in R[[X_\sigma]]$, `adicEval J x f` is Mathlib's `MvPowerSeries.eval₂` of $f$ along `algebraMap R S` and $x$, computed for the discrete topology on $R$ and the $J$-adic topology on $S$. On (coercions of) polynomials it agrees with `MvPolynomial.aeval x`, and it sends $X_s$ to $x_s$, with no further hypotheses. When $\sigma$ is finite, every $x_s$ lies in $\sqrt J$ and $S$ is $J$-adically complete, the entries $x_s$ are topologically nilpotent, `MvPowerSeries.HasEval x` holds, and $f \mapsto f(x)$ is an $R$-algebra homomorphism `adicEvalAlgHom`; moreover $f(x) \in \sqrt J$ whenever $f$ has zero constant term, and $(\mathrm{subst}\ a\ f)(x) = f\big((a_t(x))_t\big)$ for any substitutable family $a$. For an $R$-algebra map $\varphi : S \to S'$ with $J$ finitely generated and $\varphi(J) \subseteq \sqrt{J'}$, $\varphi$ is $J$-adically continuous and $\varphi(f(x)) = f\big((\varphi(x_s))_s\big)$.
--
--   The structure `Points F S J`, for a $g$-dimensional formal group law $F$ over $R$, has as fields a tuple `val : Fin g → S` together with the proof that each entry lies in $\sqrt J$. The zero tuple is always a point; for $S$ $J$-adically complete, addition is $(x+y)_i = F_i(x,y)$ and negation is $(-x)_i = \iota_i(x)$, where $\iota =$ `invSeries F` is the inverse series, and these make `Points F S J` an additive group, commutative when $F$ is commutative, with $n \cdot x$ given by the $n$-series of $F$. A homomorphism $\varphi : F \to G$ of laws induces an additive map `Hom.evalPoints` by evaluating its series, compatibly with identity, composition, zero, addition (for $G$ commutative), the ring structure of `End F` and natural-number multiples; and `Points.map` gives functoriality in $(S,J)$ under the hypotheses above, commuting with `evalPoints`.
--
--   **Relation to Mathlib.** Built on Mathlib's multivariate power series evaluation and substitution (`eval₂`, `aeval`, `HasEval`, `subst`) and on Mathlib's adic topology and `IsAdicComplete`; the formal group laws, their homomorphisms and their groups of points are the project's own notions, Mathlib having no theory of formal group laws.
--
--   **Where it is used.** The group $F(S,J)$ of points with entries in $\sqrt J$, its functoriality in $(S,J)$ and the induced action of homomorphisms and endomorphisms are the vocabulary in which torsion of formal groups over complete local rings is expressed, as needed in the local analysis of the Galois representations attached to elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_PointsV2.lean

import Definitions.Def_MvFormalGroup_NegV2
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Finiteness.Ideal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section AdicEval

variable {S : Type*} [CommRing S] [Algebra R S] {S' : Type*} [CommRing S'] [Algebra R S']
  {σ : Type*}

def adicEval (J : Ideal S) (x : σ → S) (f : MvPowerSeries σ R) : S :=
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  MvPowerSeries.eval₂ (algebraMap R S) x f

private theorem isTopologicallyNilpotent_of_mem_radical (J : Ideal S) {a : S}
    (ha : a ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    IsTopologicallyNilpotent a := by
  letI : TopologicalSpace S := J.adicTopology
  obtain ⟨k, hk⟩ := ha
  show Filter.Tendsto (a ^ ·) Filter.atTop (nhds 0)
  rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
  intro n _
  filter_upwards [Filter.eventually_ge_atTop (k * n)] with m hm
  obtain ⟨r, rfl⟩ : ∃ r, m = k * n + r := ⟨m - k * n, by omega⟩
  rw [pow_add, pow_mul]
  exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk n))

private theorem hasEval_of_mem_radical [Finite σ] (J : Ideal S) {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    MvPowerSeries.HasEval x := by
  letI : TopologicalSpace S := J.adicTopology
  refine ⟨fun s => isTopologicallyNilpotent_of_mem_radical J (hx s), ?_⟩
  rw [Filter.cofinite_eq_bot]
  exact Filter.tendsto_bot

theorem adicEval_coe (J : Ideal S) (x : σ → S) (p : MvPolynomial σ R) :
    adicEval J x (p : MvPowerSeries σ R) = MvPolynomial.aeval x p := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  rw [MvPolynomial.aeval_def]
  exact MvPowerSeries.eval₂_coe (algebraMap R S) x p

theorem adicEval_X (J : Ideal S) (x : σ → S) (s : σ) :
    adicEval J x (X s : MvPowerSeries σ R) = x s := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  exact MvPowerSeries.eval₂_X (algebraMap R S) x s

def adicEvalAlgHom [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) : MvPowerSeries σ R →ₐ[R] S :=
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  MvPowerSeries.aeval (hasEval_of_mem_radical J hx)

theorem coe_adicEvalAlgHom [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) : ⇑(adicEvalAlgHom (R := R) J hx) = adicEval J x := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  funext f
  exact congrFun (MvPowerSeries.coe_aeval (hasEval_of_mem_radical J hx)) f

open MvPowerSeries.WithPiTopology in

theorem adicEval_mem_radical [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    adicEval J x f ∈ J.radical := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  show MvPowerSeries.eval₂ (algebraMap R S) x f ∈ J.radical
  have hφ : Continuous (algebraMap R S) := continuous_of_discreteTopology
  have ha := hasEval_of_mem_radical J hx
  have hf' : IsTopologicallyNilpotent f :=
    MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero hf
  have hc : Continuous (MvPowerSeries.eval₂Hom hφ ha) := by
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.continuous_eval₂ hφ ha
  obtain ⟨n, hn⟩ := (hf'.map hc).exists_pow_mem_of_mem_nhds
    ((J.hasBasis_nhds_zero_adic).mem_of_mem (i := 1) trivial)
  rw [MvPowerSeries.coe_eval₂Hom, pow_one] at hn
  exact ⟨n, hn⟩

theorem adicEval_subst [Finite σ] {τ : Type*} (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) {a : τ → MvPowerSeries σ R} (ha : HasSubst a)
    (f : MvPowerSeries τ R) :
    adicEval J x (subst a f) = adicEval J (fun t => adicEval J x (a t)) f := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  exact MvPowerSeries.eval₂_subst ha (hasEval_of_mem_radical J hx) f

theorem map_adicEval [Finite σ] (J : Ideal S) [IsAdicComplete J S] (J' : Ideal S')
    [IsAdicComplete J' S'] (φ : S →ₐ[R] S') (hJ : J.FG) (hφ : ∀ s ∈ J, φ s ∈ J'.radical)
    {x : σ → S} (hx : ∀ s, x s ∈ J.radical) (f : MvPowerSeries σ R) :
    φ (adicEval J x f) = adicEval J' (fun s => φ (x s)) f := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  letI : WithIdeal S' := ⟨J'⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  haveI : CompleteSpace S' :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J' from rfl)).mp ‹IsAdicComplete J' S'›).1
  haveI : T2Space S' :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J' from rfl)).mp ‹IsAdicComplete J' S'›).2
  have hle : J.map (φ : S →+* S') ≤ J'.radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact hφ s hs
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (hJ.map _)
  have hcont : Continuous (φ : S →+* S') := by
    apply continuous_of_continuousAt_zero (φ : S →+* S')
    rw [ContinuousAt, map_zero,
      (J.hasBasis_nhds_zero_adic).tendsto_iff (J'.hasBasis_nhds_zero_adic)]
    intro n _
    refine ⟨m * n, trivial, fun s hs => ?_⟩
    have hpow : (J ^ (m * n)).map (φ : S →+* S') ≤ J' ^ n := by
      rw [Ideal.map_pow, pow_mul]
      exact Ideal.pow_right_mono hm n
    exact SetLike.mem_coe.mpr (hpow (Ideal.mem_map_of_mem _ (SetLike.mem_coe.mp hs)))
  have key := congrFun (MvPowerSeries.comp_eval₂ (φ := algebraMap R S) (a := x)
    continuous_of_discreteTopology (hasEval_of_mem_radical J hx) hcont) f
  rw [AlgHom.comp_algebraMap] at key
  exact key

theorem adicEval_subst_elim (F : MvFormalGroup g R) {τ : Type*} [Finite τ] (J : Ideal S)
    [IsAdicComplete J S] {w : τ → S} (hw : ∀ t, w t ∈ J.radical)
    {u v : Fin g → MvPowerSeries τ R} (hu : ∀ j, (u j).constantCoeff = 0)
    (hv : ∀ j, (v j).constantCoeff = 0) (i : Fin g) :
    adicEval J w (subst (Sum.elim u v) (F.toPowerSeries i)) =
      adicEval J (Sum.elim (fun j => adicEval J w (u j)) fun j => adicEval J w (v j))
        (F.toPowerSeries i) := by
  have hfam : (fun s => adicEval J w (Sum.elim u v s)) =
      Sum.elim (fun j => adicEval J w (u j)) fun j => adicEval J w (v j) := by
    funext s
    rcases s with j | j <;> rfl
  rw [adicEval_subst J hw (hasSubst_elim hu hv), hfam]

private theorem map_mem_radical {J : Ideal S} {J' : Ideal S'} (φ : S →ₐ[R] S')
    (hφ : ∀ s ∈ J, φ s ∈ J'.radical) {s : S} (hs : s ∈ J.radical) : φ s ∈ J'.radical := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hφ _ ha
  refine ⟨a * b, ?_⟩
  rw [pow_mul, ← map_pow φ s a]
  exact hb

end AdicEval

private theorem forall_sumElim {α β M : Type*} {p : M → Prop} {x : α → M} {y : β → M}
    (hx : ∀ a, p (x a)) (hy : ∀ b, p (y b)) : ∀ c, p (Sum.elim x y c) := by
  rintro (a | b)
  exacts [hx a, hy b]

@[ext]
structure Points (F : MvFormalGroup g R) (S : Type*) [CommRing S] (J : Ideal S) : Type _ where

  val : Fin g → S

  mem_radical : ∀ i, val i ∈ J.radical

namespace Points

variable {F : MvFormalGroup g R} {S : Type*} [CommRing S] {J : Ideal S}

instance instZero : Zero (Points F S J) := ⟨⟨fun _ => 0, fun _ => Submodule.zero_mem _⟩⟩

theorem val_zero : (0 : Points F S J).val = fun _ => 0 := rfl

variable [Algebra R S]

private theorem adicEval_X_eq (x : Points F S J) :
    (fun j => adicEval J x.val (X j : MvPowerSeries (Fin g) R)) = x.val :=
  funext fun j => adicEval_X J x.val j

variable [IsAdicComplete J S]

protected def add (x y : Points F S J) : Points F S J where
  val i := adicEval J (Sum.elim x.val y.val) (F.toPowerSeries i)
  mem_radical i := adicEval_mem_radical J (forall_sumElim x.mem_radical y.mem_radical)
    (F.constantCoeff_eq_zero i)

instance instAdd : Add (Points F S J) := ⟨Points.add⟩

theorem val_add (x y : Points F S J) (i : Fin g) :
    (x + y).val i = adicEval J (Sum.elim x.val y.val) (F.toPowerSeries i) := rfl

protected def neg (x : Points F S J) : Points F S J where
  val i := adicEval J x.val (invSeries F i)
  mem_radical i := adicEval_mem_radical J x.mem_radical (constantCoeff_invSeries F i)

instance instNeg : Neg (Points F S J) := ⟨Points.neg⟩

theorem val_neg (x : Points F S J) (i : Fin g) :
    (-x).val i = adicEval J x.val (invSeries F i) := rfl

protected theorem add_assoc (x y z : Points F S J) : x + y + z = x + (y + z) := by
  ext i
  show adicEval J (Sum.elim (fun j => adicEval J (Sum.elim x.val y.val) (F.toPowerSeries j))
        z.val) (F.toPowerSeries i)
      = adicEval J (Sum.elim x.val fun j => adicEval J (Sum.elim y.val z.val)
        (F.toPowerSeries j)) (F.toPowerSeries i)
  have hw : ∀ t, Sum.elim x.val (Sum.elim y.val z.val) t ∈ J.radical :=
    forall_sumElim x.mem_radical (forall_sumElim y.mem_radical z.mem_radical)
  have ha : ∀ j, (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R).constantCoeff
      = 0 := fun j => constantCoeff_X _
  have hb : ∀ j, (X (Sum.inr (Sum.inl j)) :
      MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R).constantCoeff = 0 := fun j => constantCoeff_X _
  have hc : ∀ j, (X (Sum.inr (Sum.inr j)) :
      MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R).constantCoeff = 0 := fun j => constantCoeff_X _
  have hxa : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)) = x.val :=
    funext fun j => adicEval_X _ _ _
  have hyb : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (X (Sum.inr (Sum.inl j)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)) = y.val :=
    funext fun j => adicEval_X _ _ _
  have hzc : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)) = z.val :=
    funext fun j => adicEval_X _ _ _
  have hin1 : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j)))
      = fun j => adicEval J (Sum.elim x.val y.val) (F.toPowerSeries j) := by
    funext j
    rw [adicEval_subst_elim F J hw ha hb, hxa, hyb]
  have hin2 : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) :
          MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)))
      = fun j => adicEval J (Sum.elim y.val z.val) (F.toPowerSeries j) := by
    funext j
    rw [adicEval_subst_elim F J hw hb hc, hyb, hzc]
  have key := congrArg (adicEval J (Sum.elim x.val (Sum.elim y.val z.val)))
    (subst_elim_assoc F ha hb hc i)
  rw [adicEval_subst_elim F J hw (constantCoeff_subst_elim F ha hb) hc,
    adicEval_subst_elim F J hw ha (constantCoeff_subst_elim F hb hc),
    hin1, hzc, hxa, hin2] at key
  exact key

protected theorem zero_add (x : Points F S J) : 0 + x = x := by
  ext i
  show adicEval J (Sum.elim (fun _ => 0) x.val) (F.toPowerSeries i) = x.val i
  have h0 : ∀ j : Fin g, (0 : MvPowerSeries (Fin g) R).constantCoeff = 0 := fun _ => map_zero _
  have hX : ∀ j : Fin g, (X j : MvPowerSeries (Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hz : (fun _ : Fin g => adicEval J x.val (0 : MvPowerSeries (Fin g) R)) = fun _ => 0 := by
    funext j
    rw [← coe_adicEvalAlgHom J x.mem_radical, map_zero]
  have key := congrArg (adicEval J x.val) (subst_elim_zero_left F hX i)
  rw [adicEval_subst_elim F J x.mem_radical h0 hX, hz, adicEval_X_eq, adicEval_X] at key
  exact key

protected theorem add_zero (x : Points F S J) : x + 0 = x := by
  ext i
  show adicEval J (Sum.elim x.val fun _ => 0) (F.toPowerSeries i) = x.val i
  have h0 : ∀ j : Fin g, (0 : MvPowerSeries (Fin g) R).constantCoeff = 0 := fun _ => map_zero _
  have hX : ∀ j : Fin g, (X j : MvPowerSeries (Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hz : (fun _ : Fin g => adicEval J x.val (0 : MvPowerSeries (Fin g) R)) = fun _ => 0 := by
    funext j
    rw [← coe_adicEvalAlgHom J x.mem_radical, map_zero]
  have key := congrArg (adicEval J x.val) (subst_elim_zero_right F hX i)
  rw [adicEval_subst_elim F J x.mem_radical hX h0, hz, adicEval_X_eq, adicEval_X] at key
  exact key

protected theorem neg_add_cancel (x : Points F S J) : -x + x = 0 := by
  ext i
  show adicEval J (Sum.elim (fun j => adicEval J x.val (invSeries F j)) x.val)
      (F.toPowerSeries i) = 0
  have hX : ∀ j : Fin g, (X j : MvPowerSeries (Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hz : adicEval J x.val (0 : MvPowerSeries (Fin g) R) = 0 := by
    rw [← coe_adicEvalAlgHom J x.mem_radical, map_zero]
  have key := congrArg (adicEval J x.val) (subst_elim_invSeries_X F i)
  rw [adicEval_subst_elim F J x.mem_radical (constantCoeff_invSeries F) hX, adicEval_X_eq,
    hz] at key
  exact key

instance instAddGroup : AddGroup (Points F S J) where
  add := (· + ·)
  zero := 0
  neg := fun x => -x
  add_assoc := Points.add_assoc
  zero_add := Points.zero_add
  add_zero := Points.add_zero
  neg_add_cancel := Points.neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

protected theorem add_comm [IsComm F] (x y : Points F S J) : x + y = y + x := by
  ext i
  show adicEval J (Sum.elim x.val y.val) (F.toPowerSeries i)
      = adicEval J (Sum.elim y.val x.val) (F.toPowerSeries i)
  have hw : ∀ t, Sum.elim x.val y.val t ∈ J.radical :=
    forall_sumElim x.mem_radical y.mem_radical
  have ha : ∀ j, (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hb : ∀ j, (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hxa : (fun j => adicEval J (Sum.elim x.val y.val)
      (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ Fin g) R)) = x.val :=
    funext fun j => adicEval_X _ _ _
  have hyb : (fun j => adicEval J (Sum.elim x.val y.val)
      (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) = y.val :=
    funext fun j => adicEval_X _ _ _
  have key := congrArg (adicEval J (Sum.elim x.val y.val)) (subst_elim_comm F ha hb i)
  rw [adicEval_subst_elim F J hw ha hb, adicEval_subst_elim F J hw hb ha, hxa, hyb] at key
  exact key

instance instAddCommGroup [IsComm F] : AddCommGroup (Points F S J) :=
  { Points.instAddGroup with add_comm := Points.add_comm }

theorem val_nsmul (n : ℕ) (x : Points F S J) :
    (n • x).val = fun i => adicEval J x.val (F.nthSeries n i) := by
  induction n with
  | zero =>
    funext i
    rw [zero_nsmul]
    show (0 : S) = adicEval J x.val (0 : MvPowerSeries (Fin g) R)
    rw [← coe_adicEvalAlgHom J x.mem_radical, map_zero]
  | succ n ih =>
    funext i
    rw [succ_nsmul]
    show adicEval J (Sum.elim (n • x).val x.val) (F.toPowerSeries i)
        = adicEval J x.val (subst (Sum.elim (F.nthSeries n) fun j => X j) (F.toPowerSeries i))
    rw [adicEval_subst_elim F J x.mem_radical (constantCoeff_nthSeries F n)
      (fun j => constantCoeff_X j), ih, adicEval_X_eq]

end Points

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R} {H : MvFormalGroup k R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]

def evalPoints (φ : Hom F G) : Points F S J →+ Points G S J :=
  AddMonoidHom.mk'
    (fun x => ⟨fun i => adicEval J x.val (φ.toPowerSeries i),
      fun i => adicEval_mem_radical J x.mem_radical (φ.constantCoeff_eq_zero i)⟩)
    (fun x y => by
      ext i
      show adicEval J (fun j => adicEval J (Sum.elim x.val y.val) (F.toPowerSeries j))
          (φ.toPowerSeries i)
        = adicEval J (Sum.elim (fun j => adicEval J x.val (φ.toPowerSeries j))
          fun j => adicEval J y.val (φ.toPowerSeries j)) (G.toPowerSeries i)
      have hw : ∀ t, Sum.elim x.val y.val t ∈ J.radical :=
        forall_sumElim x.mem_radical y.mem_radical
      have hl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have hr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have hU : ∀ j, (subst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j)).constantCoeff = 0 := fun j =>
        constantCoeff_subst_eq_zero hl (fun l => constantCoeff_X _) (φ.constantCoeff_eq_zero j)
      have hV : ∀ j, (subst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j)).constantCoeff = 0 := fun j =>
        constantCoeff_subst_eq_zero hr (fun l => constantCoeff_X _) (φ.constantCoeff_eq_zero j)
      have hxa : (fun l => adicEval J (Sum.elim x.val y.val)
          (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) = x.val :=
        funext fun l => adicEval_X _ _ _
      have hyb : (fun l => adicEval J (Sum.elim x.val y.val)
          (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) = y.val :=
        funext fun l => adicEval_X _ _ _
      have hin1 : (fun j => adicEval J (Sum.elim x.val y.val)
          (subst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j))) = fun j => adicEval J x.val (φ.toPowerSeries j) := by
        funext j
        rw [adicEval_subst J hw hl, hxa]
      have hin2 : (fun j => adicEval J (Sum.elim x.val y.val)
          (subst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j))) = fun j => adicEval J y.val (φ.toPowerSeries j) := by
        funext j
        rw [adicEval_subst J hw hr, hyb]
      have key := congrArg (adicEval J (Sum.elim x.val y.val)) (φ.subst_eq i)
      rw [adicEval_subst J hw F.hasSubst_toPowerSeries, adicEval_subst_elim G J hw hU hV,
        hin1, hin2] at key
      exact key)

theorem val_evalPoints (φ : Hom F G) (x : Points F S J) (i : Fin h) :
    (φ.evalPoints x).val i = adicEval J x.val (φ.toPowerSeries i) := rfl

theorem evalPoints_id (x : Points F S J) : (Hom.id F).evalPoints x = x := by
  ext i
  exact adicEval_X J x.val i

theorem evalPoints_comp (ψ : Hom G H) (φ : Hom F G) (x : Points F S J) :
    (ψ.comp φ).evalPoints x = ψ.evalPoints (φ.evalPoints x) := by
  ext i
  exact adicEval_subst J x.mem_radical φ.hasSubst_toPowerSeries (ψ.toPowerSeries i)

theorem evalPoints_zero (x : Points F S J) : (0 : Hom F G).evalPoints x = 0 := by
  ext i
  show adicEval J x.val (0 : MvPowerSeries (Fin g) R) = 0
  rw [← coe_adicEvalAlgHom J x.mem_radical, map_zero]

theorem evalPoints_add [IsComm G] (φ ψ : Hom F G) (x : Points F S J) :
    (φ + ψ).evalPoints x = φ.evalPoints x + ψ.evalPoints x := by
  ext i
  exact adicEval_subst_elim G J x.mem_radical φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero i

theorem evalPoints_one (x : Points F S J) : Hom.evalPoints (1 : End F) x = x :=
  evalPoints_id x

theorem evalPoints_mul (φ ψ : End F) (x : Points F S J) :
    Hom.evalPoints (φ * ψ) x = Hom.evalPoints φ (Hom.evalPoints ψ x) :=
  evalPoints_comp φ ψ x

theorem evalPoints_natCast [IsComm F] (n : ℕ) (x : Points F S J) :
    Hom.evalPoints (n : End F) x = n • x := by
  ext i
  show adicEval J x.val (Hom.toPowerSeries (n : End F) i) = (n • x).val i
  rw [End.toPowerSeries_natCast F n, Points.val_nsmul]

end Hom

namespace Points

variable {F : MvFormalGroup g R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {J' : Ideal S'} [IsAdicComplete J' S']

def map (φ : S →ₐ[R] S') (hJ : J.FG) (hφ : ∀ s ∈ J, φ s ∈ J'.radical) :
    Points F S J →+ Points F S' J' :=
  AddMonoidHom.mk'
    (fun x => ⟨fun i => φ (x.val i), fun i => map_mem_radical φ hφ (x.mem_radical i)⟩)
    (fun x y => by
      ext i
      show φ (adicEval J (Sum.elim x.val y.val) (F.toPowerSeries i))
          = adicEval J' (Sum.elim (fun j => φ (x.val j)) fun j => φ (y.val j))
            (F.toPowerSeries i)
      have hfam : (fun s => φ (Sum.elim x.val y.val s))
          = Sum.elim (fun j => φ (x.val j)) fun j => φ (y.val j) := by
        funext s
        rcases s with j | j <;> rfl
      rw [map_adicEval J J' φ hJ hφ (forall_sumElim x.mem_radical y.mem_radical), hfam])

theorem val_map (φ : S →ₐ[R] S') (hJ : J.FG) (hφ : ∀ s ∈ J, φ s ∈ J'.radical)
    (x : Points F S J) (i : Fin g) : (map φ hJ hφ x).val i = φ (x.val i) := rfl

end Points

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {J' : Ideal S'} [IsAdicComplete J' S']

theorem evalPoints_map (ψ : Hom F G) (φ : S →ₐ[R] S') (hJ : J.FG)
    (hφ : ∀ s ∈ J, φ s ∈ J'.radical) (x : Points F S J) :
    ψ.evalPoints (Points.map φ hJ hφ x) = Points.map φ hJ hφ (ψ.evalPoints x) := by
  ext i
  exact (map_adicEval J J' φ hJ hφ x.mem_radical (ψ.toPowerSeries i)).symm

end Hom

end MvFormalGroup


