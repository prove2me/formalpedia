-- Prove2me | Definitions.Def_MoranYanPAC_Main_SOA
-- name    : MoranYanPAC_Main_SOA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:04:41.365846+00:00
-- url     : https://prove2.me/theorems/8ffd8179-0bdb-46cb-afab-f2f501a71e42
-- title:
--   Static SOA with ties toward zero
-- statement:
--   For a nonempty binary class $G\subseteq\{0,1\}^X$, its **Standard Optimal Algorithm classifier** compares the Littlestone dimensions of the two subclasses with prescribed label at a query $x$:
--
--   $$\operatorname{SOA}_G(x)=\begin{cases}1,&\operatorname{LDim}(\{h\in G:h(x)=1\})>\operatorname{LDim}(\{h\in G:h(x)=0\}),\\0,&\text{otherwise}.\end{cases}$$
--
--   This is the static predictor used in the witness lemma. Empty subclasses have dimension $-1$, below every nonempty subclass. Ties choose zero, as in this source; the published online SOA uses the opposite tie convention. The harmless total value on an empty $G$ is the constant-zero predictor.
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Definition 5, p. 15 (PDF p. 15)

import Mathlib
import Definitions.Def_UnderstandingML_Online

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Definition 5, p. 15. Static SOA; the empty branch ranks below dimension zero,
and equal dimensions choose zero. The value on an empty class is zero. -/
noncomputable def SOA {X : Type*} (G : Set (X → Bool)) : X → Bool :=
  fun x => decide (UnderstandingML.ldimBot {h ∈ G | h x = false} <
    UnderstandingML.ldimBot {h ∈ G | h x = true})

end MoranYanPAC.Main


