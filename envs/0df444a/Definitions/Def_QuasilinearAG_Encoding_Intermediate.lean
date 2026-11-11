-- Prove2me | Definitions.Def_QuasilinearAG_Encoding_Intermediate
-- name    : QuasilinearAG_Encoding_Intermediate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:41:53.423728+00:00
-- url     : https://prove2.me/theorems/de76fbc5-743f-4767-8bab-7c84dc384a4a
-- title:
--   Intermediate last steps $E=F_{h-1}(z)$, $z=P_V(x_h)$: subspace polynomials $P_V$, $M_W$, and the monomials $m_{a,j}$ and $u_{a,j}=C_0^\kappa(m_{a,j})$
-- statement:
--   Inside the height-$h$ tower $F=F_h$ over the finite field $k$ (characteristic $p$, $q=p^s$), fix an additive subgroup $V$ of $k$ (equivalently an $\mathbb F_p$-subspace) contained in $C=\ker(X^q+X)$.
--
--   - $P_V(X)=\prod_{v\in V}(X-v)$, the **subspace polynomial**; $W=P_V(C)$ and $M_W(Z)=\prod_{w\in W}(Z-w)$.
--   - $\phi(y)=y^q/(1+y^{q-1})$; $F_i=k(x_0,\dots,x_i)$.
--   - $z=P_V(x_h)$ and $E=F_{h-1}(z)$, the subfield of $F$ generated over $k$ by $x_0,\dots,x_{h-1}$ and $z$.
--   - The **standard monomials of $E$** are $m_{a,j}=\prod_{i=1}^{h-1}x_i^{a_i}z^j$ with $0\le a_i<q$, $0\le j<e$ (5.4), where $e=q/|V|$; there are $D=eq^{h-1}$ of them.
--   - $u_{a,j}=C_0^\kappa(m_{a,j})$, the Cartier coefficient taken in $E$ with the same separator $t=x_0^q+x_0$, $\kappa=\lceil\log_q h\rceil+1$.
--
--   These fields supply every degree $D=eq^{h-1}$ over $k(x_0)$, which is what lets the code reach every length.
--
--   **Formalization Note** $E$ is a subfield of the given model of $F_h$ over $k$, so its places are places of $E/k$ in the sense of `Place`; $x_0$, $z$, $t$ and $x_i$ ($i<h$) are its elements.
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), §5.2 pp. 18–19 (PDF 20–21), (5.2)–(5.4)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower

namespace QuasilinearAG.Encoding

/-!
# Intermediate last steps `E = F_{h-1}(z)`, `z = P_V(x_h)` (§5.2)

Chao, Liu, Li, Ma, Wang, *Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier
Bases*, STOC 2027 submission (manuscript sha256 355c15dc…), §5.2 pp. 18–19 (PDF 20–21), (5.2)–(5.4).

Inside a model `F = F_h` of the tower (`IsGSTower`), fix an additive subgroup `V` of the finite
field `k` (in characteristic `p` this is the same as an `F_p`-subspace) contained in
`C = ker(X^q + X)`.

* `subspacePoly V = P_V(X) = Π_{v ∈ V}(X - v)`;
* `imagePoly q V = M_W(Z) = Π_{w ∈ W}(Z - w)` with `W = P_V(C)`;
* `phiField q y = ϕ(y) = y^q/(1 + y^{q-1})`;
* `lowerField x i = F_i = k(x₀, …, x_i)` inside `F`;
* `zElt q h x V = z = P_V(x_h)`;
* `interField q h x V = E = F_{h-1}(z)` as a subfield of `F` over `k` (it is generated over `k` by
  `x₀, …, x_{h-1}` and `z`);
* `xInE`, `zInE`, `x0InE`, `tInE`: the elements `x_i` (`i < h`), `z`, `x₀` and `t = x₀^q + x₀` of `E`;
* `interMono q h e x V a j = m_{a,j} = Π_{i=1}^{h-1} x_i^{a_i} z^j` (5.4), `0 ≤ a_i < q`,
  `0 ≤ j < e`;
* `interExtracted = u_{a,j} = C_0^κ(m_{a,j})`, the Cartier coefficient taken inside `E` with the
  same separator `t`, and `κ = ⌈log_q h⌉ + 1`.
-/

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- `P_V(X) = Π_{v ∈ V}(X - v)`. -/
noncomputable def subspacePoly [Fintype k] (V : AddSubgroup k) : Polynomial k := by
  classical
  exact ∏ v ∈ Finset.univ.filter (fun c => c ∈ V), (Polynomial.X - Polynomial.C v)

/-- `M_W(Z) = Π_{w ∈ W}(Z - w)`, `W = P_V(C)`, `C = ker(X^q + X)`. -/
noncomputable def imagePoly [Fintype k] (q : ℕ) (V : AddSubgroup k) : Polynomial k := by
  classical
  exact ∏ w ∈ Finset.univ.filter
      (fun w => ∃ c : k, c ^ q + c = 0 ∧ (subspacePoly V).eval c = w),
    (Polynomial.X - Polynomial.C w)

/-- `ϕ(y) = y^q / (1 + y^{q-1})`. -/
noncomputable def phiField (q : ℕ) (y : F) : F := y ^ q / (1 + y ^ (q - 1))

/-- `F_i = k(x₀, …, x_i)`. -/
def lowerField (x : ℕ → F) (i : ℕ) : IntermediateField k F :=
  IntermediateField.adjoin k (x '' Set.Iic i)

/-- `z = P_V(x_h)`. -/
noncomputable def zElt [Fintype k] (h : ℕ) (x : ℕ → F) (V : AddSubgroup k) : F :=
  Polynomial.aeval (x h) (subspacePoly V)

/-- `E = F_{h-1}(z) = k(x₀, …, x_{h-1}, z)`. -/
noncomputable def interField [Fintype k] (h : ℕ) (x : ℕ → F) (V : AddSubgroup k) :
    IntermediateField k F :=
  IntermediateField.adjoin k (x '' Set.Iio h ∪ {x 0, zElt h x V})

/-- `x_i` as an element of `E`, for `i < h`. -/
noncomputable def xInE [Fintype k] (h : ℕ) (x : ℕ → F) (V : AddSubgroup k) (i : ℕ) (hi : i < h) :
    interField h x V :=
  ⟨x i, IntermediateField.subset_adjoin k _ (Or.inl ⟨i, hi, rfl⟩)⟩

/-- `x₀` as an element of `E`. -/
noncomputable def x0InE [Fintype k] (h : ℕ) (x : ℕ → F) (V : AddSubgroup k) : interField h x V :=
  ⟨x 0, IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))⟩

/-- `z` as an element of `E`. -/
noncomputable def zInE [Fintype k] (h : ℕ) (x : ℕ → F) (V : AddSubgroup k) : interField h x V :=
  ⟨zElt h x V, IntermediateField.subset_adjoin k _ (Or.inr (Or.inr rfl))⟩

/-- The separator `t = x₀^q + x₀` as an element of `E`. -/
noncomputable def tInE [Fintype k] (q h : ℕ) (x : ℕ → F) (V : AddSubgroup k) : interField h x V :=
  x0InE h x V ^ q + x0InE h x V

/-- `m_{a,j} = Π_{i=1}^{h-1} x_i^{a_i} z^j` (5.4); `a i` is the exponent of `x_{i+1}`. -/
noncomputable def interMono [Fintype k] (q h e : ℕ) (x : ℕ → F) (V : AddSubgroup k)
    (aj : (Fin (h - 1) → Fin q) × Fin e) : interField h x V :=
  (∏ i : Fin (h - 1), xInE h x V ((i : ℕ) + 1) (by omega) ^ ((aj.1 i : ℕ))) *
    zInE h x V ^ ((aj.2 : ℕ))

/-- `u_{a,j} = C_0^κ(m_{a,j})`, extracted inside `E` with the separator `t = x₀^q + x₀`. -/
noncomputable def interExtracted [Fintype k] (q h e : ℕ) (x : ℕ → F) (V : AddSubgroup k)
    (aj : (Fin (h - 1) → Fin q) × Fin e) : interField h x V :=
  (cartierCoeff q (tInE q h x V) 0)^[kappaOf q h] (interMono q h e x V aj)

end QuasilinearAG.Encoding


