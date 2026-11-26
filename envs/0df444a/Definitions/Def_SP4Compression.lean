-- Prove2me | Definitions.Def_SP4Compression
-- name    : SP4Compression
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-26T11:01:15.687647+00:00
-- url     : https://prove2.me/theorems/1d8658b6-da9c-4da7-808e-8584ce7bdd06
-- title:
--   Cell-compressibility of a pointed space pair
-- statement:
--   A space pair $(Y,\{y\})$ is **cell-compressible at** $y$ if every based generalized $n$-loop in $Y$ — every continuous map $g:I^n\to Y$ carrying the boundary $\partial I^n$ into $y$ — is homotopic relative to $\partial I^n$ to the constant loop at $y$:
--   $$\forall n,\ \forall g:(I^n,\partial I^n)\to(Y,y),\quad g\simeq_{\partial I^n}\mathrm{const}_y .$$
--   This is precisely the vanishing of the relative homotopy groups $\pi_n(Y,\{y\})$ in every degree.  In Mathlib the absolute group $\pi_n(Y,y)$ is the quotient of based generalized $n$-loops by exactly this rel-boundary relation, so cell-compressibility follows directly from $\mathrm{Subsingleton}\,\pi_n(Y,y)$ — this direction is proved outright in the reduction.
-- source:
--   同伦论(2) Whitehead定理与胞腔逼近, 知乎专栏 https://zhuanlan.zhihu.com/p/22412267564 (压缩引理的胞腔归纳证明); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Lemma 4.7 (compression lemma).

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false

universe v

namespace SP4Compression

/-- Cell-compressibility of the pair `(Y, {y})`: every based generalized `n`-loop in `Y`,
i.e. every continuous map of the `n`-cube sending the boundary to `y`, is homotopic relative
to the boundary to the constant loop at `y`.

This is exactly the vanishing of the relative homotopy groups `π_n(Y, {y})` for all `n`
(the point-pair case of the compression lemma's hypothesis).  It is provable in Mathlib
from `Subsingleton (HomotopyGroup.Pi n Y y)`, since `π_n` is the quotient of generalized
loops by rel-boundary homotopy. -/
def CellCompressible (Y : Type v) [TopologicalSpace Y] (y : Y) : Prop :=
  ∀ n : ℕ, ∀ g : GenLoop (Fin n) Y y,
    Nonempty (GenLoop.Homotopic g (GenLoop.const : GenLoop (Fin n) Y y))

end SP4Compression


