-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
-- name    : OAI_Algebra_AffineCancellation_Cylinder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:50:08.83483+00:00
-- url     : https://prove2.me/theorems/5d126295-d536-4395-ae93-523862eaf852
-- title:
--   Explicit isomorphism $A[t]\cong\mathbb{C}[p,s,u,F,J]$ for the hypersurface ring $A=\mathbb{C}[p,s,u,F,J]/(H)$
-- statement:
--   Let $P=\mathbb{C}[p,s,u,F,J]$ be the polynomial ring in five variables over $\mathbb{C}$, and put
--   $$x=s^2+u^3+p^2F,\qquad H=x^2F-(1+2sx)J-p^2J^2-pu,\qquad A=P/(H).$$
--   Bars denote classes in $A$, and $A[t]$ is the polynomial ring in one variable over $A$. For a commutative ring $R$, a point is $q=(q_p,q_s,q_u,q_f,q_j)\in R^5$ and $E(q)$ is the value of $H$ at $q$, i.e. $E(q)=x^2q_f-(1+2q_sx)q_j-q_p^2q_j^2-q_pq_u$ with $x=q_s^2+q_u^3+q_p^2q_f$. A frame is $\tau=(\tau_p,\tau_s,\tau_u,\tau_m)\in R^4$. The maps $\mathrm{enc}:R^5\times R\to R^4\times R$ and $\mathrm{dec}:R^4\times R\to R^5\times R$ are the explicit integer polynomial encoding and decoding maps of the cylinder construction: $\mathrm{enc}(q,w)$ is the frame of the shifted point $\sigma_{-w}(q)$ together with one further coordinate, and $\mathrm{dec}(\tau,z)$ is a shifted point on the frame line of $\tau$ together with the shift parameter. They satisfy $E(\mathrm{dec}(\tau,z)_1)=0$ and $\mathrm{enc}\circ\mathrm{dec}=\mathrm{id}$. They also satisfy $\mathrm{dec}(\mathrm{enc}(q,w))=(q,w)$ whenever $E(q)=0$ and $q_p^3r=0$ forces $r=0$, and they commute with ring homomorphisms.
--
--   The file builds the following.
--
--   1. **Regularity lemmas.** (a) If $R$ is an integral domain, $p\in R$ is prime and $p\nmid h$, then the class of $p$ is a non-zero-divisor in $R/(h)$. (b) If $r$ is a non-zero-divisor of a commutative ring $R$, then the constant polynomial $r$ is a non-zero-divisor of $R[t]$.
--
--   2. **Universal point and frame.** The point $(p,s,u,F,J)\in P^5$ and the frame $\theta=(p,s,u,F)\in P^4$, in which the variable $F$ plays the role of the frame coordinate $\tau_m$.
--
--   3. **Evaluation.** For a commutative $\mathbb{C}$-algebra $R$ and a point $q$, $\mathrm{ev}_q:P\to R$ is the $\mathbb{C}$-algebra homomorphism $(p,s,u,F,J)\mapsto(q_p,q_s,q_u,q_f,q_j)$. Then $\mathrm{ev}_q(H)=E(q)$, evaluation at the universal point is the identity of $P$, and $g\circ\mathrm{ev}_q=\mathrm{ev}_{g(q)}$ for every $\mathbb{C}$-algebra homomorphism $g$. For a frame $\tau$ and $z\in R$, the point $\hat\tau(z)=(\tau_p,\tau_s,\tau_u,\tau_m,z)$ has the property that $\mathrm{ev}_{\hat\tau(z)}$ maps $\theta$ to $\tau$ and $J$ to $z$.
--
--   4. **Regularity of $p$.** $p\nmid H$ in $P$ (at the point $(0,0,0,0,1)$ the polynomial $H$ takes the value $-1$). Hence $\bar p$ is a non-zero-divisor of $A$ and of $A[t]$, and $\bar p^3r=0$ implies $r=0$ in $A[t]$.
--
--   5. **Source point.** $q_A=(\bar p,\bar s,\bar u,\bar F,\bar J)$, viewed as constants in $A[t]^5$; it satisfies $E(q_A)=0$.
--
--   6. **Model point.** $(q_M,w_M)=\mathrm{dec}(\theta,J)\in P^5\times P$; it satisfies $E(q_M)=0$.
--
--   7. **The two maps.** $\kappa:A\to P$ is the $\mathbb{C}$-algebra homomorphism induced by $\mathrm{ev}_{q_M}$, which is well defined because $\mathrm{ev}_{q_M}(H)=E(q_M)=0$. The map $\Phi:A[t]\to P$ is the $\mathbb{C}$-algebra homomorphism extending $\kappa$ with $\Phi(t)=w_M$. With $(\tau,z)=\mathrm{enc}(q_A,t)$, the map $\Psi:P\to A[t]$ is $\Psi=\mathrm{ev}_{\hat\tau(z)}$.
--
--   8. **The isomorphism.** $\Phi\circ\Psi=\mathrm{id}_P$ and $\Psi\circ\Phi=\mathrm{id}_{A[t]}$, so
--   $$\Phi:\ A[t]\xrightarrow{\ \sim\ }\mathbb{C}[p,s,u,F,J]$$
--   is an isomorphism of $\mathbb{C}$-algebras with inverse $\Psi$.
--
--   This is the stabilization part of the cancellation counterexample: adjoining one polynomial variable to $A$ gives a polynomial ring in five variables. The map $\kappa=\Phi|_A$ is injective, which shows that $A$ is an integral domain. Since $A$ is Noetherian, $\dim A+1=\dim A[t]=5$, so $A$ has Krull dimension $4$.
--
--   **Formalization Note** $P$ is `MvPolynomial (Fin 5) ℂ` with `X 0, …, X 4` named `p, s, u, F, J`, and $A$ is `P ⧸ Ideal.span {H}`. Non-zero-divisors are expressed with `IsLeftRegular`. In Lean, $\theta$ is `parameters`, $\hat\tau(z)$ is `paramPoint`, $q_A$ is `sourcePoint`, $(q_M,w_M)$ is `model`, $\kappa$ is `coefficientMap`, $\Phi$ is `forward` and $\Psi$ is `backward`. The final isomorphism is `equivalence : Polynomial A ≃ₐ[ℂ] P`, built with `AlgEquiv.ofAlgHom` from `forward_backward` and `backward_forward`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Cylinder.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Cylinder.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps

namespace OAI

noncomputable section

namespace ComplexCancellation.Cylinder

/-- Saturation needed at p=0. It does not assume the hypersurface is integral. -/
lemma regular_quotient_of_prime {R : Type*} [CommRing R] [IsDomain R]
    {p h : R} (hp : Prime p) (hph : ¬p ∣ h) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {h}) p) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hq
  obtain ⟨c, hc⟩ := hq
  have hpc : p ∣ c := (hp.dvd_or_dvd (show p ∣ h * c by rw [← hc]; exact dvd_mul_right _ _)).resolve_left hph
  obtain ⟨d, rfl⟩ := hpc
  have hr : r = h * d := by
    apply mul_left_cancel₀ hp.ne_zero
    linear_combination hc
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hr]
  exact dvd_mul_right _ _

lemma polynomial_C_regular {R : Type*} [CommRing R] {r : R} (hr : IsLeftRegular r) :
    IsLeftRegular (Polynomial.C r) := by
  intro f g hfg
  apply Polynomial.ext
  intro n
  apply hr
  simpa using congrArg (fun f : Polynomial R => f.coeff n) hfg

end ComplexCancellation.Cylinder

namespace ComplexCancellation.Cylinder

open MvPolynomial

def universal : Point P := ⟨p, s, u, F, J⟩
def parameters : Frame P := ⟨p, s, u, F⟩

namespace Point
variable {R S : Type*} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]

def eval (q : Point R) : P →ₐ[ℂ] R := MvPolynomial.aeval ![q.p, q.s, q.u, q.f, q.j]

@[simp] lemma universal_eval (q : Point R) : universal.map q.eval.toRingHom = q := by
  ext <;> simp [universal, map, eval, ComplexCancellation.p, ComplexCancellation.s, ComplexCancellation.u, F, J]

lemma eval_equation (q : Point R) : q.eval H = q.equation := by
  have h := universal.map_equation q.eval.toRingHom
  rw [universal_eval] at h
  exact h.symm

lemma map_eval (q : Point R) (g : R →ₐ[ℂ] S) :
    g.comp q.eval = (q.map g.toRingHom).eval := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [eval, map]

@[simp] lemma universal_eval_id : universal.eval = AlgHom.id ℂ P := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [eval, universal, ComplexCancellation.p, ComplexCancellation.s, ComplexCancellation.u, F, J]

end Point

def paramPoint {R : Type*} (t : Frame R) (z : R) : Point R := ⟨t.p, t.s, t.u, t.m, z⟩

lemma paramPoint_map {R S : Type*} [CommRing R] [CommRing S]
    (t : Frame R) (z : R) (g : R →+* S) :
    (paramPoint t z).map g = paramPoint (t.map g) (g z) := rfl

lemma parameters_eval {R : Type*} [CommRing R] [Algebra ℂ R] (t : Frame R) (z : R) :
    parameters.map (paramPoint t z).eval.toRingHom = t ∧
    (paramPoint t z).eval J = z := by
  constructor
  · ext <;> simp [parameters, Frame.map, paramPoint, Point.eval, p, s, u, F]
  · simp [paramPoint, Point.eval, J]

lemma p_not_dvd : ¬ p ∣ H := by
  intro h
  let q : Point ℂ := ⟨0, 0, 0, 0, 1⟩
  have h' := map_dvd q.eval h
  have hp : q.eval p = 0 := by simp [Point.eval, p, q]
  have hh : q.eval H = -1 := by rw [q.eval_equation]; norm_num [Point.equation, Point.x, q]
  rw [hp, hh, zero_dvd_iff] at h'
  norm_num at h'

lemma p_regular : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {H}) p) :=
  regular_quotient_of_prime (MvPolynomial.X_prime (i := 0)) p_not_dvd

def sourcePoint : Point (Polynomial A) :=
  universal.map ((Polynomial.CAlgHom : A →ₐ[ℂ] Polynomial A).comp
    (Ideal.Quotient.mkₐ ℂ (Ideal.span {H}))).toRingHom

lemma source_equation : sourcePoint.equation = 0 := by
  rw [sourcePoint, Point.map_equation]
  change Polynomial.C (Ideal.Quotient.mk (Ideal.span {H}) H) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton H)), Polynomial.C_0]

lemma source_p_regular : IsLeftRegular sourcePoint.p := polynomial_C_regular p_regular

lemma source_p_cube (r : Polynomial A) (h : sourcePoint.p ^ 3 * r = 0) : r = 0 :=
  isLeftRegular_iff_right_eq_zero_of_mul.mp (source_p_regular.pow 3) r h

def model : Point P × P := decode parameters J

lemma model_equation : model.1.equation = 0 := decode_equation _ _

def coefficientMap : A →ₐ[ℂ] P :=
  Ideal.Quotient.liftₐ (Ideal.span {H}) model.1.eval (by
    have hle : Ideal.span {H} ≤ RingHom.ker model.1.eval.toRingHom := by
      apply Ideal.span_le.mpr
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      change model.1.eval H = 0
      rw [Point.eval_equation, model_equation]
    exact fun r hr => hle hr)

def forward : Polynomial A →ₐ[ℂ] P :=
  Polynomial.eval₂AlgHom coefficientMap model.2 (fun _ => Commute.all _ _)

def backward : P →ₐ[ℂ] Polynomial A :=
  (paramPoint (encode sourcePoint Polynomial.X).1 (encode sourcePoint Polynomial.X).2).eval

@[simp] lemma forward_X : forward Polynomial.X = model.2 := by simp [forward]

@[simp] lemma coefficientMap_mk (r : P) :
    coefficientMap (Ideal.Quotient.mk (Ideal.span {H}) r) = model.1.eval r := by
  exact Ideal.Quotient.lift_mk _ _ _

@[simp] lemma forward_C (r : A) : forward (Polynomial.C r) = coefficientMap r := by
  simp [forward]

lemma forward_source : sourcePoint.map forward.toRingHom = model.1 := by
  apply Point.ext <;>
    simp [sourcePoint, Point.map, universal, Point.eval, p, s, u, F, J]

lemma forward_backward : forward.comp backward = AlgHom.id ℂ P := by
  have he := encode_map sourcePoint Polynomial.X forward.toRingHom
  rw [forward_source] at he
  change ((encode sourcePoint Polynomial.X).1.map forward.toRingHom,
    forward (encode sourcePoint Polynomial.X).2) = encode model.1 (forward Polynomial.X) at he
  rw [forward_X] at he
  change _ = encode (decode parameters J).1 (decode parameters J).2 at he
  rw [encode_decode] at he
  unfold backward
  rw [Point.map_eval (R := Polynomial A) (S := P) _ forward, paramPoint_map]
  have he₁ : (encode sourcePoint Polynomial.X).1.map forward.toRingHom = parameters :=
    congrArg Prod.fst he
  have he₂ : forward.toRingHom (encode sourcePoint Polynomial.X).2 = J :=
    congrArg Prod.snd he
  rw [he₁, he₂]
  exact Point.universal_eval_id

lemma backward_model :
    (model.1.map backward.toRingHom, backward model.2) = (sourcePoint, Polynomial.X) := by
  have hp := parameters_eval (encode sourcePoint Polynomial.X).1 (encode sourcePoint Polynomial.X).2
  have hd := decode_map (R := P) (S := Polynomial A) parameters J backward.toRingHom
  have hp₁ : parameters.map backward.toRingHom = (encode sourcePoint Polynomial.X).1 := hp.1
  have hp₂ : backward.toRingHom J = (encode sourcePoint Polynomial.X).2 := hp.2
  rw [hp₁, hp₂] at hd
  exact hd.trans (decode_encode sourcePoint Polynomial.X source_equation source_p_cube)

lemma backward_forward : backward.comp forward = AlgHom.id ℂ (Polynomial A) := by
  apply Polynomial.algHom_ext'
  · apply Ideal.Quotient.algHom_ext ℂ
    apply MvPolynomial.algHom_ext
    intro i
    have h := congrArg (fun q : Point (Polynomial A) =>
      ![q.p, q.s, q.u, q.f, q.j] i) (congrArg Prod.fst backward_model)
    simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      forward_C, coefficientMap_mk, AlgHom.id_apply]
    fin_cases i <;>
      simpa [Point.eval, sourcePoint, Point.map, universal, p, s, u, F, J] using h
  · simpa using congrArg Prod.snd backward_model

/-- The explicit scalar-preserving polynomial cylinder isomorphism. -/
def equivalence : Polynomial A ≃ₐ[ℂ] P :=
  AlgEquiv.ofAlgHom forward backward forward_backward backward_forward

end ComplexCancellation.Cylinder

end

end OAI


